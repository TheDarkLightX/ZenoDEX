"""Public M6 safe-mount reference surface.

Importing this facade exposes the immutable contract, pure transition, and
ZRPF candidate verifier without importing any integration adapter.
"""

from . import (
    m6_assurance_gates_v1 as _m6_assurance_gates_v1,
)
from . import (
    m6_authority_evidence_v1 as _m6_authority_evidence_v1,
)
from . import (
    m6_safe_mount_types_v1 as _m6_safe_mount_types_v1,
)
from . import (
    m6_zrpf_v1 as _m6_zrpf_v1,
)
from .m6_assurance_gates_v1 import *  # noqa: F401,F403
from .m6_authority_evidence_v1 import *  # noqa: F401,F403
from .m6_safe_mount_transition_v1 import run_m6_transition_v1
from .m6_safe_mount_types_v1 import *  # noqa: F401,F403
from .m6_zrpf_v1 import *  # noqa: F401,F403

__all__ = [
    *_m6_assurance_gates_v1.__all__,
    *_m6_safe_mount_types_v1.__all__,
    *_m6_authority_evidence_v1.__all__,
    *_m6_zrpf_v1.__all__,
    "run_m6_transition_v1",
]

del _m6_assurance_gates_v1, _m6_authority_evidence_v1, _m6_safe_mount_types_v1, _m6_zrpf_v1
