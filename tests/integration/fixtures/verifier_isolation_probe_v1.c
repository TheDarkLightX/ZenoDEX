/* Harmless, test-owned capability probes. Never a cryptographic verifier. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/capability.h>
#include <pthread.h>
#include <sched.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

static void *wait_for_release(void *argument) {
    char byte;
    return read(*(int *)argument, &byte, 1) == 0 ? NULL : (void *)1;
}

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
    } else if (!strcmp(mode, "hold")) {
        puts("READY");
        fflush(stdout);
        char byte;
        if (read(STDIN_FILENO, &byte, 1) != 1) return 3;
        puts("DONE");
    } else if (!strcmp(mode, "environment")) {
        const char *expected[] = { "RISC0_DEV_MODE=0", "LC_ALL=C", "PWD=/" };
        int seen[3] = {0}, exact = 1, count = 0;
        for (char **entry = environ; *entry; entry++) {
            int matched = 0;
            for (int index = 0; index < 3; index++) {
                if (!strcmp(*entry, expected[index]) && !seen[index]) {
                    seen[index] = 1;
                    matched = 1;
                    break;
                }
            }
            exact &= matched;
            count++;
        }
        printf("%d\n", exact && count == 3);
    } else if (!strcmp(mode, "cpu")) {
        for (int index = 0; index < 4; index++) {
            pid_t child = fork();
            if (child < 0) return 3;
            if (child == 0) {
                volatile unsigned long total = 0;
                for (unsigned long step = 0; step < 100000000UL; step++) total += step;
                _exit(0);
            }
        }
        while (wait(NULL) > 0) {}
        puts("READY");
        fflush(stdout);
        char byte;
        if (read(STDIN_FILENO, &byte, 1) != 1) return 3;
        puts("DONE");
    } else if (!strcmp(mode, "memory")) {
        /* At most 576 MiB across three children, even without containment. */
        int barrier[2], ready[2];
        if (pipe(barrier) || pipe(ready)) return 3;
        for (int index = 0; index < 3; index++) {
            pid_t child = fork();
            if (child < 0) return 3;
            if (child == 0) {
                close(barrier[1]);
                close(ready[0]);
                size_t size = 192UL * 1024UL * 1024UL;
                volatile char *memory = malloc(size);
                if (!memory) _exit(4);
                for (size_t page = 0; page < size; page += 4096) memory[page] = 1;
                /* All three allocations remain live until the parent releases them. */
                if (write(ready[1], "x", 1) != 1) _exit(3);
                close(ready[1]);
                char byte;
                if (read(barrier[0], &byte, 1) != 0) _exit(3);
                _exit(0);
            }
        }
        close(barrier[0]);
        close(ready[1]);
        for (int index = 0; index < 3; index++) {
            char byte;
            if (read(ready[0], &byte, 1) != 1) return 3;
        }
        close(ready[0]);
        close(barrier[1]);
        while (wait(NULL) > 0) {}
        puts("ALLOCATED");
    } else if (!strcmp(mode, "threads")) {
        pthread_t workers[24];
        int barrier[2];
        if (pipe(barrier)) return 3;
        int spawned = 0;
        for (; spawned < 24; spawned++) {
            if (pthread_create(&workers[spawned], NULL, wait_for_release, &barrier[0])) break;
        }
        close(barrier[1]);
        for (int index = 0; index < spawned; index++) {
            void *result;
            if (pthread_join(workers[index], &result) || result) return 3;
        }
        close(barrier[0]);
        printf("%d\n", spawned);
    } else if (!strcmp(mode, "tasks")) {
        /* A bounded fork probe, not an unbounded process bomb. */
        int barrier[2];
        if (pipe(barrier)) return 3;
        int spawned = 0;
        for (; spawned < 24; spawned++) {
            pid_t child = fork();
            if (child < 0) break;
            if (child == 0) {
                close(barrier[1]);
                char byte;
                if (read(barrier[0], &byte, 1) != 0) _exit(3);
                _exit(0);
            }
        }
        close(barrier[0]);
        close(barrier[1]);
        while (wait(NULL) > 0) {}
        printf("%d\n", spawned);
    } else {
        return 2;
    }
    return 0;
}
