/*
 * VOSYS internal functionalities
 *
 * THIS FILE SHOULD BE REMOVED BEFORE SHARING WITH UPSTREAM
 *
 * Copyright 2017 Virtual Open Systems
 *
 * Authors:
 *  Kevin Pouget  <k.pouget@virtualopensystems.com>
 *
 *
 */

#ifndef VOSYS_INTERNAL_H
#define VOSYS_INTERNAL_H

#include <stdint.h>
#include "vosys-internal-dist.h"


#ifndef VOSYS_VERBOSE_LEVEL
#define VOSYS_VERBOSE_LEVEL 1
#endif

#define RAM_CHECKSUM_ALL_MEMORIES 0

extern int vosys_verbose;

#define vosys_debug(fmt, ...)                                      \
    do {                                                           \
        if (vosys_verbose >= 3) {                                  \
            fprintf(stderr, "DEBUG: %s:%d ", __func__, __LINE__);  \
            fprintf(stderr, fmt, ## __VA_ARGS__);                  \
            fprintf(stderr, "\n");                                 \
        }                                                          \
    } while (0)

#define vosys_info(fmt, ...)                                        \
    do {                                                            \
        if (vosys_verbose >= 2) {                                   \
            fprintf(stderr, "INFO:  %s:%d ", __func__, __LINE__);   \
            fprintf(stderr, fmt, ## __VA_ARGS__);                   \
            fprintf(stderr, "\n");                                  \
        }                                                           \
    } while (0)

#define vosys_warning(fmt, ...)                                         \
    do {                                                                \
        if (vosys_verbose >= 1) {                                       \
            fprintf(stderr, "WARN:  %s:%d ", __func__, __LINE__);       \
            fprintf(stderr, fmt, ## __VA_ARGS__);                       \
            fprintf(stderr, "\n");                                      \
        }                                                               \
    } while (0)

#define vosys_error(fmt, ...)                                           \
    do {                                                                \
        if (vosys_verbose >= 0) {                                       \
            fprintf(stderr, "ERROR: %s:%d ", __func__, __LINE__);       \
            fprintf(stderr, fmt, ## __VA_ARGS__);                       \
            fprintf(stderr, "\n");                                      \
        }                                                               \
    } while (0)

void vosys_crash(const char *msg);

void vosys_init(int incoming_migration);

const char *vosys_get_qemu_id(void);

void fuse_handle_qmp(const char *p);
void fuse_do_reload(int64_t cpt_id);

extern int uffd_use_old_interface;

#endif /* VOSYS_INTERNAL_H */
