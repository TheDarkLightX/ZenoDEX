# Docker Hash-Locked Deployment

`Dockerfile.hashlocked` is the production-strict image path for ZenoDEX.

It exists separately from the general `Dockerfile` so release and production
gates can target a stable, explicit contract without changing existing build or
compose entry points in one step.

## Build

Build the image with:

```bash
docker build -f Dockerfile.hashlocked -t zenodex:hashlocked .
```

The image:

- installs Python dependencies from `requirements-core.lock.txt`;
- uses `pip install --require-hashes -r requirements-core.lock.txt`;
- keeps `API_HOST=127.0.0.1` by default;
- keeps the final runtime on a non-root `zenodex` user;
- copies the built UI and runtime `src/` tree only;
- does not copy `tests/` into the final production image.

## Why This Exists Separately

This path is for production-strict deployment review.

It keeps the existing Docker entry points available while giving release gates,
CI checks, and operators a dedicated image definition with an explicit
hash-locked dependency install contract.

## Recommendation

For production or production-like deployment, prefer:

```bash
docker build -f Dockerfile.hashlocked -t zenodex:prod .
```

Treat the general `Dockerfile` as compatibility or transition surface unless
the same production-strict guarantees are required and verified there too.

## Future Compose Profiles

Expected follow-on compose profiles:

- `prod-hashlocked` for the production-strict UI and API image;
- `prod-hashlocked-operator` for operator-only tools that also install from
  lockfiles;
- `dev` or `compat` profiles that can continue to use the broader image path
  while migration is in progress.

The static gate for this path is:

```bash
python3 tools/check_docker_hashlocked_install.py
```
