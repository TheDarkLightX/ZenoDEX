---
title: CONTAINER_HARDENING
type: note
permalink: autonomous-tau-dex-review/docs/container-hardening
---

# Container Hardening

The default production container is already hardened for ordinary Docker/Podman
operators:

- non-root runtime user (`zenodex`, UID/GID `10001`)
- unprivileged nginx port (`8080`)
- API bound to `127.0.0.1` by default
- `no-new-privileges:true`
- `cap_drop: [ALL]`
- read-only root filesystem
- tmpfs for writable nginx/runtime paths
- memory and PID limits
- same-origin nginx proxy with request and connection limits
- Trivy image scanning in CI and in `tools/prod_gate.sh`

## Optional AppArmor Overlay

AppArmor is host policy, so it cannot be made mandatory in the portable default
compose file. Linux operators can opt in:

```bash
sudo apparmor_parser -r .docker/apparmor/zenodex
docker compose -f docker-compose.yml -f docker-compose.apparmor.yml up -d
```

The profile is a supplement to the compose controls. It denies raw/packet
sockets, all Linux capabilities, mount/remount/umount, ptrace, and writes to
kernel control planes such as `/proc/sys`, `/sys/kernel/security`,
`/sys/kernel/debug`, and `/sys/fs/bpf`.

Quick syntax check without loading:

```bash
apparmor_parser -K -Q .docker/apparmor/zenodex
```

The repo also includes a static regression checker:

```bash
python3 tools/check_container_hardening.py
```

It checks the default compose file, optional AppArmor overlay, optional
local-node compose file, chaos compose file, Dockerfile runtime user, and the
minimum AppArmor deny/allow rules. This is not a substitute for a live
container escape audit, but it prevents accidental removal of the hardening
rails.

## Auxiliary Compose Profiles

The optional local Tau node and chaos-testing compose files now carry baseline
hardening too:

- `no-new-privileges:true`
- `cap_drop: [ALL]`
- PID and memory limits
- tmpfs for `/tmp`
- `init: true`

Those profiles are not as strict as the main production container because the
local-node helper installs dependencies into a named venv volume and the chaos
container is a testing tool. They should not be treated as the production trust
boundary.

## Seccomp

The repo currently relies on Docker/Podman's default seccomp profile. A custom
seccomp profile is possible, but it should be derived from actual runtime traces
for Python, nginx, DNS, TLS, and health checks. A hand-written deny list without
trace replay risks brittle operator failures.

## Local Validation

```bash
python3 tools/check_container_hardening.py
docker compose -f docker-compose.yml -f docker-compose.apparmor.yml config
docker compose -f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node config
docker compose -f docker-compose.chaos.yml config
bash tools/prod_gate.sh
```

The production gate builds the image and blocks on fixable HIGH/CRITICAL Trivy
findings.
