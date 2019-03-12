/*
 * QEMU live migration via generic fd
 *
 * Copyright Red Hat, Inc. 2009-2016
 *
 * Authors:
 *  Chris Lalancette <clalance@redhat.com>
 *  Daniel P. Berrange <berrange@redhat.com>
 *
 * This work is licensed under the terms of the GNU GPL, version 2.  See
 * the COPYING file in the top-level directory.
 *
 * Contributions after 2012-01-13 are licensed under the terms of the
 * GNU GPL, version 2 or (at your option) any later version.
 */

#include "qemu/osdep.h"
#include "channel.h"
#include "fd.h"
#include "qapi/error.h"
#include "migration.h"
#include "monitor/monitor.h"
#include "io/channel-util.h"
#include "trace.h"
#include "qemu/cutils.h"
#include "migration/migration.h"
#include "qemu/error-report.h"
#include "vosys-internal.h"

bool migration_is_squashing(void);

void fd_start_outgoing_migration(MigrationState *s, const char *fdname,
                                int outfd, Error **errp)
{
    QIOChannel *ioc;
    int fd = fdname ? monitor_get_fd(cur_mon, fdname, errp) : outfd;
    if (fd == -1) {
        return;
    }

    trace_migration_fd_outgoing(fd);
    ioc = qio_channel_new_fd(fd, errp);
    if (!ioc) {
        close(fd);
        return;
    }

    qio_channel_set_name(QIO_CHANNEL(ioc), "migration-fd-outgoing");
    migration_channel_connect(s, ioc, NULL, NULL);
    object_unref(OBJECT(ioc));
}

static int checkpoint_save_metadata(bool is_incremental, const char *filename) {
    unsigned long metadata_magic = CHPT_META_MAGIC;
    int bits_to_write = sizeof(checkpoint_file_state);
    int bits_written;
    int flags = O_WRONLY;
    int fd;
    int ret = 1;

    if (!is_incremental) {
        flags |= O_CREAT | O_TRUNC;
    }

    fd = qemu_open(filename, flags, S_IRUSR | S_IWUSR);
    if (fd < 0) {
        error_report("Could not open file '%s' :(", filename);

        return -1;
    }

    if (qemu_write_full(fd, &metadata_magic, sizeof(metadata_magic))
        != sizeof(metadata_magic)) {
        error_report("Could not save magic number into '%s'", filename);

        ret = -1;
        goto finish;
    };

    bits_written = qemu_write_full(fd, &checkpoint_file_state, bits_to_write);

    if (bits_written != bits_to_write) {
        error_report("Could not write the checkpoint metadata "
                     "(only %d bits written instead of %d)",
                     bits_written, bits_to_write);
        ret = -1;
    }

finish:
    qemu_close(fd);

    return ret;
}

void file_start_outgoing_migration(MigrationState *s, const char *filename,
                                   Error **errp)
{
    int fd;
    int flags;

    s->snapshot_is_incremental = migrate_use_incremental()
        && s->in_snapshot
        && checkpoint_state.snapshot_number != 0
        && access(filename, F_OK) != -1 ;

    if (migrate_use_incremental()) {
        if (!checkpoint_save_metadata(snapshot_is_incremental(), filename)) {
            error_setg_errno(errp, errno, "Failed to open file to save metadata: %s", filename);

            return;
        }

        flags = O_APPEND;
    } else {
        flags = O_CREAT;
    }

    fd = qemu_open(filename, flags | O_WRONLY, S_IRUSR | S_IWUSR);
    if (fd < 0) {
        error_setg_errno(errp, errno, "Failed to open file: %s", filename);
        return;
    }

    fd_start_outgoing_migration(s, NULL, fd, errp);
}


static gboolean fd_accept_incoming_migration(QIOChannel *ioc,
                                             GIOCondition condition,
                                             gpointer opaque)
{
    migration_channel_process_incoming(ioc);
    object_unref(OBJECT(ioc));
    return G_SOURCE_REMOVE;
}

void fd_start_incoming_migration(const char *infd, int fd, Error **errp)
{
    QIOChannel *ioc;
    long in_fd;
    int err;

    if (infd) {
        err = qemu_strtol(infd, NULL, 0, &in_fd);
        if (err < 0) {
            error_setg_errno(errp, -err, "Failed to convert string '%s'"
                            " to number", infd);
            return;
        }
        fd = (int)in_fd;
    }

    trace_migration_fd_incoming(fd);

    ioc = qio_channel_new_fd(fd, errp);
    if (!ioc) {
        close(fd);
        return;
    }

    qio_channel_set_name(QIO_CHANNEL(ioc), "migration-fd-incoming");
    qio_channel_add_watch_full(ioc, G_IO_IN,
                               fd_accept_incoming_migration,
                               NULL, NULL,
                               g_main_context_get_thread_default());
}

void file_start_incoming_migration(const char *filename, Error **errp)
{
    int fd;

    fd = qemu_open(filename, O_RDONLY);
    if (fd < 0) {
        error_setg_errno(errp, errno, "Failed to open file:%s", filename);
        return;
    }
    fd_start_incoming_migration(NULL, fd, NULL);
}

int file_get_checkpoint_fd(int snapshot_number)
{

    int fd = qemu_dup(checkpoint_state.reload_fd);
    uint64_t to_skip;

    if (fd < 0) {
        error_report("file_get_checkpoint_fd (qemu_dup) failed: %m");
        return -1;
    }

    if (snapshot_number == 0 && !checkpoint_file_state[0].is_set) {
        // not a multi-increment file
        to_skip = 0; // rewind to the beginning
    } else {
        int i;

        to_skip = sizeof(checkpoint_file_state) + sizeof(long int);
        for (i = 0; i < snapshot_number; i++) {
            assert(checkpoint_file_state[i].is_set);
            to_skip += checkpoint_file_state[i].end_of_file_offset;
        }
    }

    lseek(fd, to_skip, SEEK_SET);

    return fd;
}

void file_start_incoming_checkpoint_reload(const char *filename, int do_squash,
                                           Error **errp)
{
    int fd;

    char *split = strchr(filename, ':');

    if (split) {
        if (sscanf(filename, "%d", &checkpoint_state.reload_stop_at) != 1) {
            error_setg(errp, "Expected to find a number "
                       "in the filename before the ':'...");
        }
        vosys_debug("Reloading %d increments from %s",
                    checkpoint_state.reload_stop_at, filename);
        filename = split + 1;
    } else {
        checkpoint_state.reload_stop_at = -1;
    }

    if (do_squash) {
        checkpoint_state.do_squash = filename;
    } else {
      checkpoint_state.do_squash = NULL;
    }

    checkpoint_state.in_checkpoint_reloading = true;
    checkpoint_state.snapshot_number = 0;

    fd = qemu_open(filename, O_RDONLY);
    if (fd < 0) {
        error_setg_errno(errp, errno,
                         "Failed to open checkpoint file at '%s'",
                         filename);
        return;
    }
    checkpoint_state.reload_fd = fd;
    fd_start_incoming_migration(NULL, fd, NULL);
}
