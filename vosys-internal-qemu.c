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

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include "vosys-internal.h"
#include "migration/guest-inform.h"

void vosys_init(int incoming_migration) {
    vosys_info("<VOSYS init>");

    if (uffd_use_old_interface == -1) {
         vosys_info("UFFD disabled.");
    } else {
        vosys_info("Using old UFFD interface? %s", uffd_use_old_interface ? "yes" : "no");
    }

    vosys_info("Automount fuse FS");
    fuse_handle_qmp("");

    vosys_info("Qemu ID: %s", vosys_get_qemu_id());

    guest_inform_init();

    vosys_info("</VOSYS init>\n");
}

const char *vosys_get_qemu_id(void) {
#define VOSYS_QEMU_ID_MAX_LEN 64
    static char qemu_id[VOSYS_QEMU_ID_MAX_LEN];
    static int has_qemu_id = 0;

    if (has_qemu_id) {
        return qemu_id;
    }

    const char *vm_uid_str = getenv("VM_UID");
    const char *vm_id_str = getenv("VM_ID");

    has_qemu_id = 1;
    if (vm_uid_str) {
        if (strlen(vm_uid_str) > VOSYS_QEMU_ID_MAX_LEN) {
            vosys_info("VM_UID string too long ... (max: %d chars)\n", VOSYS_QEMU_ID_MAX_LEN);
            abort();
        }
        snprintf(qemu_id, VOSYS_QEMU_ID_MAX_LEN, "%s", vm_uid_str);
    } else {

        if (vm_id_str) {
            snprintf(qemu_id, VOSYS_QEMU_ID_MAX_LEN, "%s.%s", getenv("USER"), getenv("VM_ID"));
        } else {
            snprintf(qemu_id, VOSYS_QEMU_ID_MAX_LEN, "%s.%d", getenv("USER"), getpid());
        }
    }

    return qemu_id;
}
