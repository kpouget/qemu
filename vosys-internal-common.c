#include <stdio.h>
#include "vosys-internal.h"

#ifndef VOSYS_AWAIT_DBG_ON_CRASH
#define VOSYS_AWAIT_DBG_ON_CRASH 0
#endif

void vosys_crash(const char *msg) {
    fprintf(stderr, "FATAL: %s\n", msg);
#if VOSYS_AWAIT_DBG_ON_CRASH == 1
    fprintf(stderr, "FATAL: connect a debugging to PID %d  / LWP %ld "  \
            "and `set var blocked = 0` to continue.\n",
            getpid(), syscall(SYS_gettid));
    register volatile int blocked = 1;
    while(blocked);
#endif
}

int vosys_verbose = VOSYS_VERBOSE_LEVEL;
