from __future__ import annotations

from typing import TYPE_CHECKING

from ..composer import MethodAutoProof

if TYPE_CHECKING:
    from ..ast import StructuredStatement
    from ..composer import Composer, Proof


class HypothesisProver:
    """
    Prove the claim by some hypothesis
    """

    @staticmethod
    def prove_notation_statement(composer: Composer, target: StructuredStatement) -> Proof:
        for essential in composer.get_all_essentials():
            if essential.statement.terms == target.terms:
                return essential.apply()
        raise AssertionError(f'failed to prove {target} using a hypothesis')

    auto = MethodAutoProof(prove_notation_statement.__func__)  # type: ignore
