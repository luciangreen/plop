"""plop analysis stages."""

from .stage1 import IRClause, analyse_file as analyse_stage1_file, analyse_source as analyse_stage1_source
from .stage2 import analyse_file, analyse_source

__all__ = [
    "IRClause",
    "analyse_file",
    "analyse_source",
    "analyse_stage1_file",
    "analyse_stage1_source",
]
