# F04A plan: bind acknowledgment progress to prior state

Status: implemented and tested in the isolated public research slice.

## Objective

Supply the missing prior-state relation for distinguishing a legitimate
pending acknowledgment from deletion or mutation of an acknowledgment that
was already durable.

## Procedure

1. Reopen both prior and current payloads through F04.
2. Compare the complete non-ack projections and reject history changes.
3. Require the prior acknowledgment set to be a subset of the current set.
4. Require every common acknowledgment row to remain byte-identical.
5. Derive current pending effects from the complete outbox projection.
6. Return typed `pending` or `acked` progress evidence.

## Nonclaims

F04A does not decide current-only missing acknowledgments without prior state,
authenticate destination evidence, or establish production delivery and
recovery behavior.
