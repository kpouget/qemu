#include <stdio.h>
#include "vosys-internal-dist.h"
#include "migration/guest-inform.h"

#ifndef USE_GUEST_INFO
#define USE_GUEST_INFO 0
#endif

#if USE_GUEST_INFO == 1

#define GUEST_INFORM_HOST_SOCKET "/tmp/qemu_guest_inform.sock"

int guest_inform_sock = 0;

static void host_connect_chardev(void)
{
	struct sockaddr_un sock;
	int ret;

	guest_inform_sock = socket(AF_UNIX, SOCK_STREAM, 0);
	if (guest_inform_sock == -1)
		vosys_error("socket failed");

	sock.sun_family = AF_UNIX;
	memcpy(&sock.sun_path, GUEST_INFORM_HOST_SOCKET, sizeof(sock.sun_path));
	ret = connect(guest_inform_sock, (struct sockaddr *)&sock, sizeof(sock));
	/*
	 * It's ok if we can't connect to the control port in case
	 * we're running on old qemu
	 */
	if (ret < 0) {
		vosys_debug("%s: Can't open connection to %s\n",
                    __func__, GUEST_INFORM_HOST_SOCKET);
	}
}

static void guest_inform_write(char c) {
    if (guest_inform_sock) {
        int i =  write(guest_inform_sock, &c, sizeof(c));
        if (i != sizeof(c)) {
            vosys_debug("wrote only %d bytes\n", i);
        }
    } else {
        vosys_error("guest-inform not connected ...\n");
    }
}

void guest_inform_checkpoint_started(void) {
    vosys_error("Inform the guest of the checkpoint start");
    guest_inform_write('c');
}
void guest_inform_checkpoint_finished(void) {
    vosys_error("Inform the guest that the checkpoint is finished");
    guest_inform_write('C');
}

static int reload_count = 0;
void guest_inform_reload(void) {
    vosys_error("Inform the guest of the reload!");
    guest_inform_write('R');
    assert(reload_count < 10);
    guest_inform_write('0'+reload_count);
    reload_count += 1;
}

static void *guest_inform_thread(void *opaque) {
    char msg = 'X';
    Error *err = NULL;

    ssize_t read_sz;

    vosys_info("Hello from the guest-inform thread !");

    while (true) {
        read_sz = read(guest_inform_sock, &msg, sizeof(msg));
        if (read_sz == -1) {
            vosys_info("read error !");
            sleep(1);
            continue;
        }
        if (read_sz == 0) {
            break;
        }
        vosys_debug("read %c\n", msg);
        switch (msg) {
        case 'r':
            vosys_error("Do a reload\n");
            fuse_do_reload(0);
            break;
            ;;
        case 'c':
            vosys_error("Do a checkpoint\n");
            qmp_migrate("chpt:", 0, 0, 0, 0, false, false, false, 0, &err);
            break;
            ;;
        case 'q':
            vosys_error("Quit\n");
            qmp_quit(NULL);
            break;
            ;;
        case 'h':
            vosys_error("Hello :-)\n");
            break;
            ;;

        case '\n':
            break;;

        default:
            vosys_error("Action '%c' not recognized\n", msg);
        }
    }
    vosys_info("Bye-bye from the guest-inform thread !");

    return NULL;
}
void guest_inform_init(void) {
    vosys_info("guest-inform: module enabled. Don't forget to connect it!");
}


void guest_inform_connect(void) {
    static QemuThread thread;

    host_connect_chardev();

    vosys_error("Guest-inform FD is %d", guest_inform_sock);

    qemu_thread_create(&thread, "migrate/guest-inform", guest_inform_thread, NULL,
                       QEMU_THREAD_JOINABLE);

}


#else
void guest_inform_init(void) {
     vosys_info("guest-inform: module not enabled.");
}
void guest_inform_connect(void) {}
void guest_inform_checkpoint_started(void) {}
void guest_inform_checkpoint_finished(void) {}
void guest_inform_reload(void) {}
#endif
