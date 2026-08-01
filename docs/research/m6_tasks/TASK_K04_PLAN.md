# K04 plan: anchored TCG publisher topology

Status: implemented and tested as a pinned research root relation;
deployment-complete topology remains open.

## Objective

Anchor the reviewed publisher topology to the D05 inventory and the detailed
K01 entrypoint inventory. Require a reviewed root update when a publisher,
source path, upstream root, or unique-port identity changes.

## Procedure

1. Rebuild D05 and K01 from their source configurations.
2. Require their exact pinned roots and the expected K01 publisher set.
3. Union and canonically order their source paths.
4. Bind the unique K02 port ID and derive the domain-separated K04 root.
5. Compare the derived root to the externally reviewed K04 pin and generated
   vector.
6. Preserve publisher insertion, source insertion, D05 root substitution,
   and noncanonical-order negative witnesses.

## Evidence boundary

K04 does not perform the K07 production deployment audit, prove complete
runtime reachability, or prove a mounted no-bypass theorem. It is a root
integrity relation over reviewed inputs.
