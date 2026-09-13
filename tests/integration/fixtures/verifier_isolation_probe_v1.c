/* Harmless, test-owned capability probes. Never a cryptographic verifier. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/capability.h>
#include <sched.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

int main(void) {
    char mode[16], argument[1024];
    if (scanf("%15s %1023s", mode, argument) != 2) return 2;
    if (!strcmp(mode, "read") || !strcmp(mode, "write")) {
        int flags = !strcmp(mode, "read") ? O_RDONLY : O_WRONLY | O_TRUNC;
        int fd = open(argument, flags);
        int saved_errno = errno;
        if (fd >= 0) {
            if (flags != O_RDONLY && write(fd, "changed", 7) != 7) return 3;
            close(fd);
        }
        printf("%d %d\n", fd >= 0, fd >= 0 ? 0 : saved_errno);
    } else if (!strcmp(mode, "network")) {
        struct sockaddr_un address = { .sun_family = AF_UNIX };
        size_t length = strlen(argument);
        if (length >= sizeof(address.sun_path) - 1) return 2;
        memcpy(address.sun_path + 1, argument, length);
        int fd = socket(AF_UNIX, SOCK_STREAM, 0);
        if (fd < 0) return 3;
        int connected = connect(fd, (struct sockaddr *)&address,
            offsetof(struct sockaddr_un, sun_path) + length + 1) == 0;
        close(fd);
        printf("%d\n", connected);
    } else if (!strcmp(mode, "privileges")) {
        struct __user_cap_header_struct header = { _LINUX_CAPABILITY_VERSION_3, 0 };
        struct __user_cap_data_struct capabilities[2] = {0};
        if (syscall(SYS_capget, &header, &capabilities)) return 3;
        int no_new_privileges = prctl(PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0);
        int user_namespace = unshare(CLONE_NEWUSER);
        printf("%d %u %u %d\n", no_new_privileges,
            capabilities[0].effective, capabilities[1].effective, user_namespace);
    } else if (!strcmp(mode, "escape")) {
        pid_t child = fork();
        if (child < 0) return 3;
        if (child == 0) {
            int blocker[2];
            if (setsid() < 0 || pipe(blocker)) _exit(3);
            puts("READY");
            fflush(stdout);
            char byte;
            /* Both ends stay open: the child waits until the test kills it. */
            if (read(blocker[0], &byte, 1) != 1) _exit(3);
            _exit(0);
        }
        return waitpid(child, NULL, 0) < 0 ? 3 : 0;
    } else {
        return 2;
    }
    return 0;
}
