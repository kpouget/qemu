/*
  FUSE: Filesystem in Userspace
  Copyright (C) 2001-2006  Miklos Szeredi <miklos@szeredi.hu>

  This program can be distributed under the terms of the GNU GPL.
  See the file COPYING.

  gcc -Wall `pkg-config fuse --cflags --libs` hello.c -o hello
*/

#define FUSE_USE_VERSION 26

#include <signal.h>

#include "qemu/osdep.h"
#include "qemu/cutils.h"
#include "qemu/error-report.h"
#include "qemu/main-loop.h"
#include "qemu/thread.h"
#include "exec/target_page.h"
#include "sysemu/sysemu.h"
#include "qapi/qapi-commands-migration.h"
#include "qapi/qapi-commands-misc.h"
#include "migration/migration.h"
#include "ram.h"
#include "migration/guest-inform.h"

#include "hw/hw.h"

#include "vosys-internal.h"

#include <fuse/fuse.h>
#include <fuse/fuse_common_compat.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>

int vosys_fuse_verbose = 1;

#define vosys_fuse_debug(fmt, ...)                                      \
    do {                                                           \
        if (vosys_fuse_verbose >= 3) {                                  \
            fprintf(stderr, "DEBUG: %s:%d ", __func__, __LINE__);  \
            fprintf(stderr, fmt, ## __VA_ARGS__);                  \
            fprintf(stderr, "\n");                                 \
        }                                                          \
    } while (0)

#define vosys_fuse_info(fmt, ...)                                        \
    do {                                                            \
        if (vosys_fuse_verbose >= 2) {                                   \
            fprintf(stderr, "INFO:  %s:%d ", __func__, __LINE__);   \
            fprintf(stderr, fmt, ## __VA_ARGS__);                   \
            fprintf(stderr, "\n");                                  \
        }                                                           \
    } while (0)

#define vosys_fuse_warning(fmt, ...)                                         \
    do {                                                                \
        if (vosys_fuse_verbose >= 1) {                                       \
            fprintf(stderr, "WARN:  %s:%d ", __func__, __LINE__);       \
            fprintf(stderr, fmt, ## __VA_ARGS__);                       \
            fprintf(stderr, "\n");                                      \
        }                                                               \
    } while (0)

#define vosys_fuse_error(fmt, ...)                                           \
    do {                                                                \
        if (vosys_fuse_verbose >= 0) {                                       \
            fprintf(stderr, "ERROR: %s:%d ", __func__, __LINE__);       \
            fprintf(stderr, fmt, ## __VA_ARGS__);                       \
            fprintf(stderr, "\n");                                      \
        }                                                               \
    } while (0)

typedef enum {
    FUSE_OPEN = 0,
    FUSE_UTIMENS,
    FUSE_READDIR,
    FUSE_TESTDIR,

    FUSE_GETATTR,
    FUSE_READ_BUF,
    FUSE_WRITE_BUF,
    FUSE_TRUNCATE,
    FUSE_FLUSH,
    FUSE_RELEASE,

    FUSE_LAST
} FuseOperation;

#define FUSE_FILE_READ (1 << 0)
#define FUSE_FILE_WRITE (1 << 1)
#define FUSE_FILE_RW (FUSE_FILE_READ|FUSE_FILE_WRITE)

#define FUSE_INT_MAX_SIZE 16


struct fuse_arguments;
struct fuse_action;

typedef struct fuse_action {
    const char *name_template;
    const char *path;
    /* returns:
     * >0 if could not trigger,
     *  0 is triggering was successful
     * <0 if the triggering raised an error */
    int (*trigger)(struct fuse_arguments *);
    struct fuse_action *content;
    bool disabled;
    void *opaque;
} fuse_action;

struct fuse_arguments {
    FuseOperation type;
    struct fuse_action *self;
    const char *path;
    struct fuse_file_info *fi;
    size_t ret;
    void *opaque;

    union {
        struct {
            struct timespec tv[2];
        } utimens;
        struct {
            struct fuse_file_info *fi;
        } open;
        struct {
            struct stat *stbuf;
        } getattr;
        struct {
            fuse_fill_dir_t filler;
            void *buf;
        } readdir;
        struct {
            struct fuse_bufvec **bufp;
            size_t size;
            off_t offset;
        } read_buf;
        struct {
            struct fuse_bufvec *buf;
            off_t offset;
        } write_buf;
    };
};

static
struct fuse_action *fuse_get_action(const char *path,
                                    struct fuse_action *self);
static int fuse_migrate_treat_file(struct fuse_arguments *arg, int mode);

struct fuse_file_handler {
    int was_written;

    char *buffer;
    size_t size;

    char *current_position;
    size_t remaining_size;
};

static
struct fuse_file_handler *fuse_prepare_str_fh(char *buffer) {
    struct fuse_file_handler *fh = g_malloc(sizeof(*fh));

    size_t sz = strlen(buffer);
    fh->buffer = buffer;

    fh->current_position = fh->buffer;
    fh->remaining_size = sz;
    fh->was_written = 0;
    fh->size = sz;

    return fh;
}

static
struct fuse_file_handler *fuse_prepare_fh_fmt(const char *fmt, ...) {
    char *buffer;
    int ret;
    va_list aptr;

    va_start(aptr, fmt);
    ret = vasprintf(&buffer, fmt, aptr);
    va_end(aptr);

    if (!ret) {
        vosys_fuse_error("Error in asprintf");
        return NULL;
    }

    return fuse_prepare_str_fh(buffer);
}

static
struct fuse_file_handler *fuse_prepare_fh_string(const char *val) {
    return fuse_prepare_fh_fmt("%s", val);
}

static
struct fuse_file_handler *fuse_prepare_empty_fh_buffer(const size_t sz) {
    struct fuse_file_handler *fh = g_malloc(sizeof(*fh));

    fh->buffer = g_malloc(sz);
    fh->current_position = fh->buffer;
    fh->remaining_size = sz;
    fh->was_written = 0;
    fh->size = sz;

    return fh;
}

static int treat_time_since_last(struct fuse_arguments *arg) {
    int ret;

    if (arg->type == FUSE_OPEN) {
        int time_since_last = time(NULL) - checkpoint_state.last_checkpoint_ts;

        vosys_fuse_info("GIVE time since last checkpoint: %d", time_since_last);
        arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%ds\n", time_since_last);

        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;
    }


    return 1;
}

static int treat_nb_dirty_pages(struct fuse_arguments *arg) {
    int ret;

    if (arg->type == FUSE_OPEN) {
        int target_pages_per_host_page = qemu_target_page_size() /  getpagesize();
        int nb_faults = snapshot_is_incremental() ?
            ram_counters.postcopy_requests * target_pages_per_host_page: -1;

        vosys_fuse_debug("GIVE %d dirty pages", nb_faults);

        arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", nb_faults);

        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;
    }

    return 1;
}

static int treat_info_pid(struct fuse_arguments *arg) {
    int ret;

    if (arg->type == FUSE_OPEN) {
        pid_t pid = getpid();
        vosys_fuse_info("Qemu PID is %d", pid);
        arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", pid);

        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;
    }

    return 1;
}

static int fuse_find_host_ram_ptr(RAMBlock *rb, void *opaque) {
    const char *block_name = qemu_ram_get_idstr(rb);
    void *host_addr = qemu_ram_get_host_addr(rb);

    if (strcmp(block_name, "mach-virt.ram") == 0) {
        void **host_ram_start_p = (void **) opaque;
        *host_ram_start_p = host_addr;
        return -1;
    }
    return 0;
}

static int fuse_find_ram_size(RAMBlock *rb, void *opaque) {
    const char *block_name = qemu_ram_get_idstr(rb);
    ram_addr_t length = qemu_ram_get_used_length(rb);

    if (strcmp(block_name, "mach-virt.ram") == 0) {
        ram_addr_t *ram_size_p = (ram_addr_t *) opaque;
        *ram_size_p = length;
        return -1;
    }
    return 0;
}

static int treat_info_host_ram_location(struct fuse_arguments *arg) {
    int ret;

    if (arg->type == FUSE_OPEN) {
        void *host_ram_ptr = NULL;
        ram_addr_t ram_size = 0;

        foreach_not_ignored_block(fuse_find_host_ram_ptr, &host_ram_ptr);
        foreach_not_ignored_block(fuse_find_ram_size, &ram_size);

        vosys_fuse_info("Qemu RAM host pointer at %p (0x%xb)", host_ram_ptr, (unsigned int) ram_size);
        arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%p:0x%x\n", host_ram_ptr, ram_size);

        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;
    }

    return 1;
}

static int treat_control_stop(struct fuse_arguments *arg) {
    if (arg->type == FUSE_UTIMENS) {
         vosys_fuse_info("Stopping Qemu ...");
         qemu_mutex_lock_iothread();
         vm_stop_force_state(RUN_STATE_PAUSED);
         qemu_mutex_unlock_iothread();
         return 0;
    }
    return 1;
}

static int treat_control_quit(struct fuse_arguments *arg) {
    if (arg->type == FUSE_UTIMENS) {
        vosys_fuse_info("Quitting QEMU ...");
        qmp_quit(NULL);
        return 0;
    }
    return 1;
}

static int treat_control_terminate(struct fuse_arguments *arg) {
    if (arg->type == FUSE_UTIMENS) {
        vosys_fuse_info("Terminating QEMU ...");
        exit(1);
        return 0;
    }
    return 1;
}

static int treat_control_segfault(struct fuse_arguments *arg) {
    if (arg->type == FUSE_UTIMENS) {
        vosys_fuse_info("Segfaulting QEMU ...");
        int *i = NULL;
        *i = 10;
        return 0;
    }
    return 1;
}

static int treat_control_guest_inform(struct fuse_arguments *arg) {
    static int inited = 0;
    if (arg->type == FUSE_UTIMENS) {
        if (!inited) {
            guest_inform_init();
            inited = 1;
        } else {
            guest_inform_checkpoint_finished();
        }
        return 0;
    }
    return 1;
}

static int treat_control_cont(struct fuse_arguments *arg) {
    if (arg->type == FUSE_UTIMENS) {
        vosys_fuse_info("Continuing QEMU ...");
        qemu_mutex_lock_iothread();
        vm_start();
        qemu_mutex_unlock_iothread();
        return 0;
    }
    return 1;
}

static int treat_control_logging_vosys(struct fuse_arguments *arg) {
    int ret;

    if (arg->type == FUSE_RELEASE) {
        struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

        if (!fh) {
            vosys_fuse_warning("No file handler received ...");

        } else if (fh->was_written) {
            int new_verbose_level;

            if (sscanf(fh->buffer, "%d", &new_verbose_level) != 1) {
                vosys_fuse_warning("Could not parse the new logging value '%s' ...", fh->buffer);
                return -EINVAL;
            }

            if (strcmp(arg->self->path, "/control/logging/vosys") == 0) {
                vosys_verbose = new_verbose_level;
                vosys_warning("VOSYS logging verbosity level set to %d.", vosys_verbose);
                vosys_error  ("Vosys ERROR test message");
                vosys_warning("Vosys WARNING test message");
                vosys_info   ("Vosys INFO test message");
                vosys_debug  ("Vosys DEBUG test message");
            } else if (strcmp(arg->self->path, "/control/logging/vosys_fuse") == 0) {
                vosys_fuse_verbose = new_verbose_level;
                vosys_fuse_warning("Vosys FUSE logging verbosity level set to %d.", vosys_fuse_verbose);
                vosys_fuse_error  ("Vosys FUSE ERROR test message");
                vosys_fuse_warning("Vosys FUSE WARNING test message");
                vosys_fuse_info   ("Vosys FUSE INFO test message");
                vosys_fuse_debug  ("Vosys FUSE DEBUG test message");
            }
        }
        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;

    } else if (arg->type == FUSE_OPEN) {
        if (((arg->fi->flags & 3) == O_RDONLY)) {
            arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", vosys_fuse_verbose);
            return 0;
        } else if (arg->fi->flags & O_WRONLY) {
            arg->fi->fh = (uint64_t) fuse_prepare_empty_fh_buffer(FUSE_INT_MAX_SIZE);
            return 0;
        } else {
            return -EACCES;
        }
    }
    return 1;
}

static int treat_control_settings(struct fuse_arguments *arg) {
    MigrationCapabilityStatusList *caps, *cap;
    int ret = 1;

    if (strcmp(arg->path, arg->self->path) == 0) {
        if (arg->type == FUSE_READDIR) {
            fuse_fill_dir_t filler = arg->readdir.filler;
            void *buf = arg->readdir.buf;

            caps = qmp_query_migrate_capabilities(NULL);

            for (cap = caps; caps && cap; cap = cap->next) {
                filler(buf, qapi_enum_lookup(&MigrationCapability_lookup, cap->value->capability), NULL, 0);
            }
            qapi_free_MigrationCapabilityStatusList(caps);

            return 0;
        } else if (arg->type == FUSE_GETATTR) {
            struct stat *stbuf = arg->getattr.stbuf;

            stbuf->st_mode = S_IFDIR | 0755;
            stbuf->st_nlink = 2;
            return 0;
        }
        return 1;
    }


    const char *filename = strrchr(arg->path, '/')+1;

    caps = qmp_query_migrate_capabilities(NULL);

    for (cap = caps; cap; cap = cap->next) {
        if (strcmp(filename, qapi_enum_lookup(&MigrationCapability_lookup, cap->value->capability)) == 0) {
            break;
        }
    }

    if (!cap) {
        if (arg->type != FUSE_READDIR) {
            vosys_fuse_warning("Capability '%s' not found ...", filename);
        }
        ret = 1;
        goto cleanup;
    }

    if (arg->type == FUSE_RELEASE) {
        struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

        if (!fh) {
            vosys_fuse_debug("No file handler received ...");

        } else if (fh->was_written) {
            MigrationState *s = migrate_get_current();
            int success = 1;

            if (strcmp(fh->buffer, "on") == 0 ||
                strcmp(fh->buffer, "on\n") == 0) {
                cap->value->state = true;
            } else if (strcmp(fh->buffer, "off") == 0 ||
                       strcmp(fh->buffer, "off\n") == 0) {
                cap->value->state = false;
            } else {
                vosys_fuse_warning("Value '%s' not recognized for migration capability '%s'",
                            fh->buffer, filename);

                success = 0;
            }

            if (success) {
                s->enabled_capabilities[cap->value->capability] = cap->value->state;

                vosys_fuse_info("Migration capability '%s' %s", filename,
                            cap->value->state ? "enabled" : "disabled");
            }
            // no not return, `fuse_migrate_treat_file` should handle it
        }
    }

    const size_t content_max_size = sizeof(char)*(4+1); // 'on' or 'off' + \n
    if (arg->type == FUSE_GETATTR) {
        struct stat *stbuf = arg->getattr.stbuf;

        stbuf->st_mode = S_IFREG | 0666;
        stbuf->st_nlink = 1;
        stbuf->st_size = content_max_size;

        ret = 0;
    } else if (arg->type == FUSE_OPEN) {

        const char *val = cap->value->state ? "on\n" : "off\n";

        if ((arg->fi->flags & 3) == O_RDONLY) {
            arg->fi->fh = (uint64_t) fuse_prepare_fh_string(val);
        } else if (arg->fi->flags & O_WRONLY) {
            arg->fi->fh = (uint64_t) fuse_prepare_empty_fh_buffer(content_max_size);
        } else {
            if (arg->fi->flags & O_WRONLY) vosys_fuse_debug("O_WRONLY");
            if ((arg->fi->flags & 3) == O_RDONLY) vosys_fuse_debug("O_RDONLY");
            if (arg->fi->flags & O_RDWR) vosys_fuse_debug("O_RDWR");
            vosys_fuse_warning("Unknown open flags %d", arg->fi->flags);
            return -EACCES;
        }

        ret = 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
         // pass
    }

cleanup:
    qapi_free_MigrationCapabilityStatusList(caps);

    return ret;
}

struct checkpoint_info_opaque {
    int id;
};

static int treat_checkpoint_info_content(struct fuse_arguments *arg) {
    struct checkpoint_info_opaque *data = arg->opaque;
    struct CheckpointStats *current_stats = &checkpoint_stats[data->id];
    int ret;

    if (current_stats->is_set == STAT_UNSET) {
        vosys_fuse_warning("Checkpoint stats #%d not set, aborting ...", data->id);
        return -ENOENT;
    }

    if (arg->type == FUSE_TESTDIR) {
        return current_stats->is_set == (enum CheckpointStatsType) arg->self->opaque;
    }

    if (arg->type == FUSE_OPEN) {
        if (current_stats->is_set == STAT_RELOADING) {
            if (strcmp(arg->self->path, "/reload_time") == 0) {
                vosys_fuse_info("GIVE %f ms of reloading", current_stats->reload.reload_time);
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%.0000fms\n", current_stats->reload.reload_time);
            } else if (strcmp(arg->self->path, "/is_last") == 0) {
                vosys_fuse_info("GIVE current increment is last? %d", current_stats->reload.is_last);
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", current_stats->reload.is_last);
            }

        } else if (current_stats->is_set == STAT_CHECKPOINTING) {
            if (strcmp(arg->self->path, "/page_count") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", current_stats->checkpoint.page_count);

            } else if (strcmp(arg->self->path, "/memory_time") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%.0000fms\n", current_stats->checkpoint.memory_time);

            } else if (strcmp(arg->self->path, "/device_time") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%.0000fms\n", current_stats->checkpoint.device_time);
            } else if (strcmp(arg->self->path, "/overall_time") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%.0000fms\n", current_stats->checkpoint.overall_time);
            } else if (strcmp(arg->self->path, "/wall_time") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%d\n", current_stats->checkpoint.time);

            } else if (strcmp(arg->self->path, "/time_since_last_cpt") == 0) {
                arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("%ds\n", current_stats->checkpoint.time_since_last_cpt);
            } else {
                vosys_fuse_warning("UNKNOWN path: %s", arg->self->path);
                arg->fi->fh = (uint64_t) fuse_prepare_fh_string("unknown \n");
            }
        } else {
            vosys_fuse_warning("Invalid checkpoint stat type: %d", current_stats->is_set);
            return 1;
        }
        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_READ)) <= 0) {
        return ret;
    } else if (arg->type == FUSE_GETATTR) {
        struct stat *stbuf = arg->getattr.stbuf;

        stbuf->st_mode = S_IFREG | 0777;
        stbuf->st_nlink = data->id;
        stbuf->st_size = 127;

        return 0;
    }
    return 1;
}


static int treat_checkpoint_info(struct fuse_arguments *arg) {
    int id;

    if (arg->type == FUSE_READDIR) {

        char buffer[127];
        sprintf(buffer, "%s/", arg->path);
        if (strcmp(buffer, arg->self->path) == 0) {
            fuse_fill_dir_t filler = arg->readdir.filler;
            void *buf = arg->readdir.buf;

            int i;
            for (i = 0; checkpoint_stats[i].is_set; i++) {
                sprintf(buffer, arg->self->name_template, i);
                filler(buf, buffer, NULL, 0);
            }
            return 0;
        }
    }

    const char *path = &arg->path[strlen(arg->self->path)];

    if (sscanf(path, arg->self->name_template, &id) != 1) {
        return 1;
    }

    const char *subpath = strchr(path, '/');

    if (!subpath) {
        // path is an entry inside this directory

        if (arg->type == FUSE_GETATTR) {
            struct stat *stbuf = arg->getattr.stbuf;

            stbuf->st_mode = S_IFDIR | 0755;
            stbuf->st_nlink = 2;
            return 0;
        } else if (arg->type == FUSE_READDIR) {
            struct fuse_action *inside_self;
            arg->type = FUSE_TESTDIR;

            struct checkpoint_info_opaque opaque = {.id = id};
            arg->opaque = &opaque;

            for (inside_self = arg->self->content; inside_self->path; inside_self++) {
                arg->self = inside_self;
                if (arg->self->trigger(arg)) {
                    arg->readdir.filler(arg->readdir.buf, inside_self->path+1, NULL, 0);
                }
            }
            return 0;
        }

        return 1;
    } else {
        // subpath is an entry inside path

        struct fuse_action *inside_self = fuse_get_action(subpath, arg->self);

        if (!inside_self || !inside_self->trigger) {
            return -ENOENT;
        }

        struct checkpoint_info_opaque opaque = {.id = id};
        arg->opaque = &opaque;
        arg->self = inside_self;
        return inside_self->trigger(arg);
    }
}

static
void reset_notifier_cb(void *data) {
    int64_t id = (int64_t) data;

    vosys_fuse_info("Qemu was reset ...");
    qemu_unregister_reset(reset_notifier_cb, data);

    char filename[128];
    sprintf(filename, "%ld:/tmp/vm_checkpoint.%s", id, vosys_get_qemu_id());
    vosys_fuse_info("Reloading from '%s', until increment #%ld...",
                filename, id);

    file_start_incoming_checkpoint_reload(filename, false, NULL);
}

void fuse_do_reload(int64_t cpt_id) {
    vosys_fuse_info("Reseting the VM ...");

    qemu_register_reset(reset_notifier_cb, (void *) cpt_id);

    int current_reload = checkpoint_state.reload_number;

    qemu_system_reset_request(SHUTDOWN_CAUSE_HOST_QMP_SYSTEM_RESET);

    vosys_fuse_debug("WAIT FOR RELOAD");
    while (checkpoint_state.reload_number == current_reload) {
        g_usleep(10000);
    }
    vosys_fuse_debug("RELOADED!");
}

static int treat_reload_increment(struct fuse_arguments *arg) {
    int id;

    if (arg->type == FUSE_READDIR) {
        char buffer[127];
        sprintf(buffer, "%s/", arg->path);
        if (strcmp(buffer, arg->self->path) == 0) {
            fuse_fill_dir_t filler = arg->readdir.filler;
            void *buf = arg->readdir.buf;

            int i;
            for (i = 0; checkpoint_file_state[i].is_set; i++) {
                sprintf(buffer, arg->self->name_template, i);

                filler(buf, buffer, NULL, 0);
            }

            return 0;
        }
        return 1;
    }

    if (sscanf(&arg->path[strlen(arg->self->path)], arg->self->name_template, &id) != 1) {
        return 1;
    }

    struct CheckpointFileState *current_meta = &checkpoint_file_state[id];

#if 0 /* KP: we reload from a file, not always from memory ... */
    if (!current_meta->is_set) {
        vosys_fuse_warning("Checkpoint #%d not set, aborting ...", id);
        return -ENOENT;
    }
#endif
    if (arg->type == FUSE_UTIMENS) {
        char ts_buffer[20];
        int ret = 0;

        vosys_fuse_info("RELOAD CHECKPOINT %d !", id);

        strftime(ts_buffer, 20, "%Y-%m-%d %H:%M:%S", localtime(&current_meta->ts));
        vosys_fuse_info("Received request to reload checkpoint #%d from %s ...", id, ts_buffer);

        fuse_do_reload(id);

        return ret;

    } else if (arg->type == FUSE_GETATTR) {
        struct stat *stbuf = arg->getattr.stbuf;
        struct CheckpointFileState *current_meta = &checkpoint_file_state[id];

        stbuf->st_mode = S_IFREG | 0777;
        stbuf->st_nlink = 1;
        stbuf->st_size = 0;
        stbuf->st_atime = current_meta->ts;
        stbuf->st_ctime = current_meta->ts;
        stbuf->st_mtime = current_meta->ts;

        return 0;
    }

    return 1;
}

enum block_trigger_until_e {
    BLOCK_TRIGGER_UNTIL_NONE,
    BLOCK_TRIGGER_UNTIL_DEVICES,
    BLOCK_TRIGGER_UNTIL_MEMORY
};

int block_trigger_until = BLOCK_TRIGGER_UNTIL_DEVICES;

extern pid_t cow_checkpoint_pid;
extern struct CheckpointStats *cow_current_stats;

static int checkpoint_wait_until_finished_cow(enum block_trigger_until_e until) {
    int wstatus;
    int ret = 0;

    if (!cow_checkpoint_pid) {
        vosys_fuse_info("CoW process not forked yet ...");
        while (!cow_checkpoint_pid) {
            g_usleep(1000);
        }
    }

    vosys_fuse_info("Wait for CoW fork process (pid=%d)", cow_checkpoint_pid);
    waitpid(cow_checkpoint_pid, &wstatus, 0);
    vosys_fuse_info("CoW fork process (pid=%d) exited with code %d", cow_checkpoint_pid, wstatus);

    if (wstatus < 0) {
        ret = -EBADE;
    }

    if (cow_current_stats == NULL) {
        ret = -EINVAL;
    }

    struct CheckpointStats *current_stats = &checkpoint_stats[checkpoint_state.snapshot_cnt-1];
    memcpy(current_stats, cow_current_stats, sizeof(*cow_current_stats));
    vosys_fuse_info("Checkpoint statistics retrieved into Qemu");
    vosys_fuse_info("page count: %d", current_stats->checkpoint.page_count);

    checkpoint_file_state[checkpoint_state.snapshot_cnt - 1].end_of_file_offset = current_stats->checkpoint.end_of_file_offset;
    vosys_fuse_info("end of file: %ld", current_stats->checkpoint.end_of_file_offset);

    munmap(cow_current_stats, sizeof(*cow_current_stats));
    cow_current_stats = NULL;
    cow_checkpoint_pid = 0;

    return ret;
}

static int checkpoint_wait_until_finished(enum block_trigger_until_e until) {
    if (migrate_use_cow()) {
        return checkpoint_wait_until_finished_cow(until);
    }

    /* KP: block until setup/device/memory checkpoint is finished*/
    /* inspired from hmp_migrate_status_cb */
    int ret = 0;
    while (true) {
        if (until == BLOCK_TRIGGER_UNTIL_NONE) {
            break;
        }

        MigrationInfo *info = qmp_query_migrate(NULL);
        int status = -1;

        if (info->has_status) {
            status = info->status;
        }

        qapi_free_MigrationInfo(info);

        if (status == -1) {
            ret = -EBADMSG; // Bad message
            break;
        } else if (until == BLOCK_TRIGGER_UNTIL_DEVICES &&
                   (status == MIGRATION_STATUS_ACTIVE ||
                    status == MIGRATION_STATUS_COMPLETED)) {
            break;

        } else if (until == BLOCK_TRIGGER_UNTIL_MEMORY &&
                   status == MIGRATION_STATUS_COMPLETED) {
            break;

        } else if (status == MIGRATION_STATUS_FAILED) {
            ret = -EBADE; // Invalid exchange.
            break;
        }
        g_usleep(1000);
    }
    return ret;
}

static int treat_wait_until_cpt_finished(struct fuse_arguments *arg) {
    if (arg->type != FUSE_UTIMENS) {
        return 1;
    }

    return checkpoint_wait_until_finished(BLOCK_TRIGGER_UNTIL_MEMORY);
}

static int treat_trigger_cpt(struct fuse_arguments *arg) {
    int ret;
    Error *err = NULL;
    char block_until_arg[15];

    if (arg->type == FUSE_RELEASE) {
        struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

        if (!fh) {
            vosys_fuse_warning("No file handler received ...");

        } else if (fh->was_written) {
            int new_period;

            if (sscanf(fh->buffer, "periodic:%d", &new_period) == 1) {

                if (new_period) {
                    vosys_fuse_info("Checkpoint frequency set to '%d'", new_period);
                } else {
                    vosys_fuse_info("Periodic checkpointing disabled (period=%d).", new_period);
                }
                qmp_migrate("chpt:",
                            0, 0, // blk
                            0, 0, // inc
                            false, false, // detach
                            true, new_period, // period
                            false, false, // resume
                            &err);

            } else if (sscanf(fh->buffer, "block:%s", block_until_arg) == 1) {
                if (strcmp(block_until_arg, "none") == 0) {
                    block_trigger_until = BLOCK_TRIGGER_UNTIL_NONE;
                } else if (strcmp(block_until_arg, "devices") == 0) {
                    block_trigger_until = BLOCK_TRIGGER_UNTIL_DEVICES;
                } else if (strcmp(block_until_arg, "memory") == 0) {
                    block_trigger_until = BLOCK_TRIGGER_UNTIL_MEMORY;
                } else {
                    vosys_fuse_warning("Could not parse the 'block' argument '%s' ...", fh->buffer);
                    return -EINVAL;
                }
                vosys_fuse_info("The checkpoint trigger will blocking until '%s'.", block_until_arg);

            } else {
                vosys_fuse_warning("Could not parse the argument '%s' ...", fh->buffer);
                return -EINVAL;
            }
        }
        return 0;
    } else if ((ret = fuse_migrate_treat_file(arg, FUSE_FILE_RW)) <= 0) {
        return ret;
    } else if (arg->type == FUSE_OPEN) {

        if (((arg->fi->flags & 3) == O_RDONLY)) {
            int period;
#if 0
            MigrationState *s = migrate_get_current();

            if (s->in_periodic_checkpoint != PERIODIC_CHECKPOINT_DISABLED) {
                period = s->migration_params.period;
            } else {
                period = 0;
            }
#else
            period = -1;
            vosys_fuse_warning("periodic checkpoint frequency should be reimplemented ...");

#endif
            vosys_fuse_info("GIVE periodic checkpoint frequency: %d", period);

            arg->fi->fh = (uint64_t) fuse_prepare_fh_fmt("periodic:%d *10s\n", period);

        } else if (arg->fi->flags & O_WRONLY) {
            arg->fi->fh = (uint64_t) fuse_prepare_empty_fh_buffer(FUSE_INT_MAX_SIZE);

        } else {
            return -EACCES;
        }

        return 0;
    }

    if (arg->type != FUSE_UTIMENS) {
        return 1;
    }

    vosys_fuse_info("TRIGGER A CHECKPOINT !");

    qmp_migrate("chpt:",
                0, 0, // blk
                0, 0, // inc
                false, false, // detach
                false, false, // period
                false, false, // resume
                &err);

    return checkpoint_wait_until_finished(block_trigger_until);
}

static struct fuse_action fuse_checkpoints_reload_content[] = {
    {.path = "/checkpoints/reload/", .name_template="increment_%02d", .trigger = treat_reload_increment},
    {.path = NULL}
};

static struct fuse_action fuse_checkpoints_info_checkpoint_content[] = {
    {.path = "/reload_time", .trigger = treat_checkpoint_info_content,
    .opaque = (void *) STAT_RELOADING},
    {.path = "/is_last", .trigger = treat_checkpoint_info_content,
    .opaque = (void *) STAT_RELOADING},

    {.path = "/page_count", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = "/device_time", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = "/memory_time", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = "/overall_time", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = "/wall_time", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = "/time_since_last_cpt", .trigger = treat_checkpoint_info_content,
     .opaque = (void *) STAT_CHECKPOINTING},
    {.path = NULL}
};

static struct fuse_action fuse_checkpoints_info_content[] = {
    {.path = "/checkpoints/info/nb_dirty_pages", .trigger = treat_nb_dirty_pages},
    {.path = "/checkpoints/info/time_since_last", .trigger = treat_time_since_last},

    {.path = "/checkpoints/info/", .name_template="checkpoint_%02d",
     .trigger = treat_checkpoint_info, .content = fuse_checkpoints_info_checkpoint_content},
    {.path = NULL}
};

static struct fuse_action fuse_checkpoints_content[] = {
    {.path = "/checkpoints/trigger", .trigger = treat_trigger_cpt},
    {.path = "/checkpoints/wait_until_finished", .trigger = treat_wait_until_cpt_finished},

    {.path = "/checkpoints/reload", .content = fuse_checkpoints_reload_content},
    {.path = "/checkpoints/info", .content = fuse_checkpoints_info_content},

    {.path = NULL}
};

static struct fuse_action fuse_control_setting_content[] = {
    {.path = "/control/settings/", .name_template="%s", .trigger = treat_control_settings},
    {.path = NULL}
};

static struct fuse_action fuse_control_logging_content[] = {
    {.path = "/control/logging/vosys", .trigger = treat_control_logging_vosys},
    {.path = "/control/logging/vosys_fuse", .trigger = treat_control_logging_vosys},
    {.path = NULL}
};

static struct fuse_action fuse_control_content[] = {
    {.path = "/control/stop", .trigger = treat_control_stop},
    {.path = "/control/cont", .trigger = treat_control_cont},
    {.path = "/control/quit", .trigger = treat_control_quit},
    {.path = "/control/terminate", .trigger = treat_control_terminate},
    {.path = "/control/.segfault", .trigger = treat_control_segfault},
    {.path = "/control/.guest_inform", .trigger = treat_control_guest_inform},

    {.path = "/control/settings", .trigger = treat_control_settings,
    .content = fuse_control_setting_content
    },

    {.path = "/control/logging", .content = fuse_control_logging_content},


    {.path = NULL}
};

static struct fuse_action fuse_info_content[] = {
    {.path = "/info/pid", .trigger = treat_info_pid},
    {.path = "/info/host_ram_location", .trigger = treat_info_host_ram_location},

    {.path = NULL}
};

static struct fuse_action fuse_root_content[] = {
    {.path = "/control", .content = fuse_control_content},
    {.path = "/checkpoints", .content = fuse_checkpoints_content},
    {.path = "/info", .content = fuse_info_content},
    {.path = NULL},
};

static struct fuse_action fuse_root = {
    .path = "/", .content = fuse_root_content
};

static
struct fuse_action *fuse_get_action(const char *path,
                                    struct fuse_action *self) {
    if (!self) {
        self = &fuse_root;
    }

    if (!self->name_template && strcmp(path, self->path) == 0) {
        return self;

    } else if (self->name_template && strstart(path, self->path, NULL)) {
        return self;
    }

    if (self->content) {
        struct fuse_action *inside_self = self->content;

        for (inside_self = self->content; inside_self->path; inside_self++) {
            if (inside_self->disabled) {
                continue;
            }
            struct fuse_action *found_inside = fuse_get_action(path, inside_self);
            if (found_inside) {
                return found_inside;
            }
        }
    }
    return NULL;
}

static int fuse_migrate_getattr(const char *path, struct stat *stbuf)
{
    struct fuse_action *self = fuse_get_action(path, NULL);
    vosys_fuse_debug("GETATTR: %s", path);

    memset(stbuf, 0, sizeof(struct stat));

    if (!self) {
        vosys_fuse_info("GETATTR: fuse_action not found for '%s'", path);

        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_GETATTR,
        .self = self,
        .path = path,
        .getattr.stbuf = stbuf,
    };

    if (self->trigger) {
        int ret = self->trigger(&arg);
        vosys_fuse_debug("GETATTR: triggered %s", self->path);
        if (ret < 1) {
            return ret;
        }
    }

    if (self->content) {
        /* default dir  */
        stbuf->st_mode = S_IFDIR | 0755;
        stbuf->st_nlink = 2;

        return 0;

    } else {
        /* default file  */
        stbuf->st_mode = S_IFREG | 0444;
        stbuf->st_nlink = 1;
        stbuf->st_size = 127;
        return 0;
    }
}

static int fuse_migrate_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
                                off_t offset, struct fuse_file_info *fi)
{
    struct fuse_action *self = fuse_get_action(path, NULL);
    struct fuse_action *inside_self;
    vosys_fuse_debug("READDIR: %s", path);

    if (!self) {
        return -ENOENT;
    }
    vosys_fuse_debug("READDIR: serve %s", self->path);

    filler(buf, ".", NULL, 0);
    filler(buf, "..", NULL, 0);

    struct fuse_arguments arg = {
        .type = FUSE_READDIR,
        .self = self,
        .path = path,

        .readdir = {
            .filler = filler,
            .buf = buf,
        }
    };


    if (self->trigger) {
        int ret = self->trigger(&arg);
        if (ret < 1) {
            return ret;
        }
    }

    if (self->name_template) {
        return -ENOENT;
    }

    for (inside_self = self->content; inside_self->path; inside_self++) {
        if (inside_self->disabled) {
            continue;
        }

        if (inside_self->trigger) {
            arg.self = inside_self;
            int ret = inside_self->trigger(&arg);
            if (ret < 0) {
                return ret;
            }
        }

        if (inside_self->name_template) {
            continue;
        }

        char *fname = strrchr(inside_self->path, '/')+1;

        filler(buf, fname, NULL, 0);
    }
    return 0;
}

static int fuse_migrate_open(const char *path, struct fuse_file_info *fi)
{
    vosys_fuse_debug("OPEN: %s", path);

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_OPEN,
        .self = self,
        .path = path,
        .fi   = fi,
    };

    int ret = self->trigger(&arg);

    if (ret < 0) {
        return ret;
    }

    if (ret == 1) {
        /* not handled */
        arg.fi->fh = (uint64_t) fuse_prepare_fh_fmt("%s: open not supported.\n", path);
        ret = 0;
    }

    return 0;
}

static int fuse_migrate_flush(const char* path, struct fuse_file_info* fi) {
    vosys_fuse_debug("FLUSH: %s", path);

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_FLUSH,
        .self = self,
        .path = path,
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        /* not handled */
        ret = fuse_migrate_treat_file(&arg, FUSE_FILE_WRITE);
    }

    return ret < 1 ? ret : -ENOTSUP;
}

static int fuse_migrate_utimens(const char *path, const struct timespec tv[2]) {
    vosys_fuse_debug("UTIMENS: %s", path);

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_UTIMENS,
        .self = self,
        .path = path,
        .utimens.tv[0] = tv[0],
        .utimens.tv[1] = tv[1],
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        /* not handled */
        ret = 0;
    }

    return ret < 1 ? ret : -ENOTSUP;
}

static int fuse_migrate_write_buf (const char *path, struct fuse_bufvec *buf, off_t offset,
                                   struct fuse_file_info *fi) {
    vosys_fuse_debug("WRITE_BUF");

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_WRITE_BUF,
        .self = self,
        .path = path,
        .fi = fi,

        .write_buf = {
            .buf = buf,
            .offset = offset,
        }
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        ret = fuse_migrate_treat_file(&arg, FUSE_FILE_WRITE);
    }

    if (ret < 0) {
        return ret;
    } else if (ret == 0) {
        return arg.ret;
    } else {
        return -ENOTSUP;
    }
}

static int fuse_migrate_read_buf (const char *path, struct fuse_bufvec **bufp,
                                  size_t size, off_t offset, struct fuse_file_info *fi) {
    vosys_fuse_debug("READ_BUF");

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_READ_BUF,
        .self = self,
        .path = path,
        .fi = fi,

        .read_buf = {
            .bufp = bufp,
            .size = size,
            .offset = offset,
        }
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        ret = fuse_migrate_treat_file(&arg, FUSE_FILE_READ);
    }

    return ret < 1 ? ret : -ENOTSUP;
}

static int fuse_migrate_truncate (const char *path, off_t offset) {
    vosys_fuse_debug("TRUNCATE");

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_TRUNCATE,
        .self = self,
        .path = path,
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        ret = fuse_migrate_treat_file(&arg, FUSE_FILE_READ);
    }

    return ret < 1 ? ret : -ENOTSUP;
}

static int fuse_migrate_release (const char *path, struct fuse_file_info *fi) {
    vosys_fuse_debug("RELEASE");

    struct fuse_action *self = fuse_get_action(path, NULL);

    if (!self || !self->trigger) {
        return -ENOENT;
    }

    struct fuse_arguments arg = {
        .type = FUSE_RELEASE,
        .self = self,
        .path = path,
        .fi   = fi
    };

    int ret = self->trigger(&arg);

    if (ret == 1) {
        ret = fuse_migrate_treat_file(&arg, FUSE_FILE_READ);
    }

    return ret < 1 ? ret : -ENOTSUP;
}

/* returns <= 0 if the operation failed
 * returns 0 if the operation successed
 * returns 1 if the operation was not treated
 */

static int fuse_migrate_treat_file(struct fuse_arguments *arg, int mode) {
    if (arg->type == FUSE_TRUNCATE) {
        vosys_fuse_debug("TRUNCATE ");

        return 0;

    } else if (arg->type == FUSE_READ_BUF) {
        struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

        if (!(mode | FUSE_FILE_READ)) {
            return -EACCES;
        }
        if (!fh) {
            return -ENODEV;
        }
        size_t size = arg->read_buf.size > fh->remaining_size ? fh->remaining_size : arg->read_buf.size;

        char *buffer = malloc(size);

        struct fuse_bufvec *src = malloc(sizeof(*src));

        if (src == NULL || buffer == NULL) {
            return -ENOMEM;
        }

        memcpy(buffer, fh->current_position, size);

        *src = FUSE_BUFVEC_INIT(size);

        src->buf[0].flags = 0;
        src->buf[0].mem = buffer; // buffer must be mallocated
        src->buf[0].size = size;
        src->off = arg->read_buf.offset;

        *arg->read_buf.bufp = src;

        fh->current_position += size;
        fh->remaining_size -= size;

        return 0;

    } else if (arg->type == FUSE_WRITE_BUF) {
        struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

        if (!(mode | FUSE_FILE_WRITE)) {
            return -EACCES;
        }

        if (!fh) {
            return -ENODEV;
        }

        size_t len_rq = fuse_buf_size(arg->write_buf.buf);

        size_t size = len_rq > fh->remaining_size ?
            fh->remaining_size : len_rq;

        struct fuse_bufvec src =  FUSE_BUFVEC_INIT(size);

        src.buf[0].mem = fh->current_position;

        fuse_buf_copy(&src, arg->write_buf.buf, 0);

        vosys_fuse_debug("write: %s", fh->buffer);
        arg->ret = size;

        fh->current_position += size;
        fh->remaining_size -= size;
        /* KP: there is always 1 byte free until the end, see fuse_prepare_fh_buffer. */
        *fh->current_position = '\0';

        fh->was_written = 1;

        return 0;

    } else if (arg->type == FUSE_FLUSH) {
        vosys_fuse_debug("flush");

        return 0;
    } else if (arg->type == FUSE_RELEASE) {
        vosys_fuse_debug("release");
        if (arg->fi->fh) {
            struct fuse_file_handler *fh = (struct fuse_file_handler *) arg->fi->fh;

            if (fh->buffer) {
                g_free(fh->buffer);
            }

            g_free(fh);
        }
        return 0;
    }
    return 1;
}


static struct fuse_operations fuse_migrate_oper = {
    .getattr    = fuse_migrate_getattr,
    .readdir    = fuse_migrate_readdir,
    .open       = fuse_migrate_open,
    .utimens    = fuse_migrate_utimens,
    .read_buf   = fuse_migrate_read_buf,
    .write_buf  = fuse_migrate_write_buf,
    .truncate   = fuse_migrate_truncate,
    .flush      = fuse_migrate_flush,
    .release    = fuse_migrate_release,
};


static int fuse_in_a_fork = 0;
static void fuse_atfork_prepare(void) {}
static void fuse_atfork_parent(void) {}
static void fuse_atfork_child(void) {
    fuse_in_a_fork = 1;
}


Notifier fuse_exit_notifier;
char *mount_point;

static void fuse_exit_notify(Notifier *notifier /* not used */,
                             void *data /* not used */) {
    if (fuse_in_a_fork) {
        return;
    }

    fuse_unmount_compat22(mount_point);

    if (rmdir(mount_point) != 0) {
        perror("rmdir fuse dir");
    }
    g_free(mount_point);
    vosys_fuse_info("Byebye! Qemu ID was %s", vosys_get_qemu_id());
}

static void *fuse_thread(void *opaque) {
    char fuse_fsname[65];
    const char *qemu_id = vosys_get_qemu_id();

    mount_point = opaque;

    snprintf(fuse_fsname, sizeof(fuse_fsname), "fsname=fuse.qemu.%s", qemu_id);

    // <fsname> on <mount_point> type fuse.<subtype>
    const char *argv[] = {"_not_used_",
                          "-o", "subtype=qemu",
                          "-o", "allow_root",
                          "-o", fuse_fsname,
                          //"-o", "debug",
                          "-f", mount_point};
    /* KP: "-oauto_unmount" cannot be used because it conflicts with
     * rmdir at exit ... (Device or resource busy) */

    vosys_fuse_info("Mounting qemu/fuse into '%s' ...", mount_point);

    if (mkdir(mount_point, 0777) == 0) {
        vosys_fuse_debug("Directory '%s' created.", mount_point);
    }

    pthread_atfork(fuse_atfork_prepare, fuse_atfork_parent, fuse_atfork_child);

    fuse_exit_notifier.notify = fuse_exit_notify;
    qemu_add_exit_notifier(&fuse_exit_notifier);

    fuse_main(sizeof(argv)/sizeof(char *), (char **) argv, &fuse_migrate_oper, NULL);

    return NULL;
}

void fuse_handle_qmp(const char *p) {
    static QemuThread thread;
    char *mount_point = g_malloc(128*sizeof(char));

    sprintf(mount_point, "/tmp/qemu.%s", vosys_get_qemu_id());

    qemu_thread_create(&thread, "fuse/migrate", fuse_thread, (void *) mount_point,
                       QEMU_THREAD_JOINABLE);
}
