from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from enum import IntEnum
from typing import TYPE_CHECKING, cast

if TYPE_CHECKING:
    from collections.abc import Iterator


class Instruction(IntEnum):
    List = 1

    # Patterns
    EVar = 2
    SVar = 3
    Symbol = 4
    Implication = 5
    Application = 6
    Mu = 7
    Exists = 8

    # Meta Patterns
    MetaVar = 9
    ESubst = 10
    SSubst = 11

    # Axiom Schemas
    Prop1 = 12
    Prop2 = 29  # TODO: Fix numbering
    Prop3 = 30  # TODO: Fix numbering
    Quantifier = 13
    PropagationOr = 14
    PropagationExists = 15
    PreFixpoint = 16
    Existance = 17
    Singleton = 18

    # Inference rules
    ModusPonens = 19
    Generalization = 20
    Frame = 21
    Substitution = 22
    KnasterTarski = 23

    # Meta Incference rules
    InstantiateSchema = 24

    # Stack Manipulation
    Pop = 25

    # Memory Manipulation
    Save = 26
    Load = 27

    # Journal Manipulation
    Publish = 28


class Pattern:
    @abstractmethod
    def instantiate(self, var: MetaVar, plug: Pattern) -> Pattern:
        ...


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def instantiate(self, var: MetaVar, plug: Pattern) -> EVar:
        return self


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def instantiate(self, var: MetaVar, plug: Pattern) -> SVar:
        return self


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int

    def instantiate(self, var: MetaVar, plug: Pattern) -> Symbol:
        return self


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, var: MetaVar, plug: Pattern) -> Implication:
        return Implication(self.left.instantiate(var, plug), self.right.instantiate(var, plug))

    def __repr__(self) -> str:
        return '(' + str(self.left) + ' -> ' + str(self.right) + ')'


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, var: MetaVar, plug: Pattern) -> Application:
        return Application(self.left.instantiate(var, plug), self.right.instantiate(var, plug))


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    def instantiate(self, var: MetaVar, plug: Pattern) -> Exists:
        return Exists(self.var.instantiate(var, plug), self.subpattern.instantiate(var, plug))


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def instantiate(self, var: MetaVar, plug: Pattern) -> Mu:
        return Mu(self.var.instantiate(var, plug), self.subpattern.instantiate(var, plug))


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    fresh: tuple[EVar | SVar, ...]
    positive: tuple[SVar, ...]
    negative: tuple[SVar, ...]
    application_context: tuple[EVar, ...]

    def instantiate(self, var: MetaVar, plug: Pattern) -> Pattern:
        if self == var:
            # TODO: Check meta-requirements
            return plug
        return self

    def __repr__(self) -> str:
        return str(self.name)


@dataclass(frozen=True)
class Proved:
    pattern: Pattern

    def instantiate(self, var: MetaVar, plug: Pattern) -> Proved:
        return Proved(self.pattern.instantiate(var, plug))


Stack = list[Pattern | list[Pattern] | Proved]
Memory = list[Pattern | Proved]
Journal = list[Proved]


def execute_instructions(proof: Iterator[int], stack: Stack, memory: Memory, journal: Journal) -> None:
    while True:
        try:
            instr = next(proof)
        except StopIteration:
            return

        match instr:
            case Instruction.List:
                len = next(proof)
                items = []
                for _ in range(len):
                    pattern = stack.pop()
                    assert isinstance(pattern, Pattern)
                    items.append(pattern)
                stack.append(items)

            case Instruction.EVar:
                stack.append(EVar(next(proof)))
            case Instruction.SVar:
                stack.append(SVar(next(proof)))
            case Instruction.Symbol:
                stack.append(Symbol(next(proof)))
            case Instruction.Implication:
                left = stack.pop()
                assert isinstance(left, Pattern)
                right = stack.pop()
                assert isinstance(right, Pattern)
                stack.append(Implication(left, right))
            case Instruction.Application:
                left = stack.pop()
                assert isinstance(left, Pattern)
                right = stack.pop()
                assert isinstance(right, Pattern)
                stack.append(Application(left, right))
                # TODO: Check metavariables are well named.
            case Instruction.Exists:
                var = stack.pop()
                assert isinstance(var, EVar)
                subpattern = stack.pop()
                assert isinstance(subpattern, Pattern)
                stack.append(Exists(var, subpattern))
                # TODO: Check metavariables are well named.
            case Instruction.Mu:
                var = stack.pop()
                assert isinstance(var, SVar)
                subpattern = stack.pop()
                assert isinstance(subpattern, Pattern)
                stack.append(Mu(var, subpattern))

            case Instruction.MetaVar:
                name = next(proof)
                application_context = cast('list[EVar]', stack.pop())
                # TODO: We need assertions instead of typecasting
                assert isinstance(application_context, list)
                negative = cast('list[SVar]', stack.pop())
                assert isinstance(negative, list)
                positive = cast('list[SVar]', stack.pop())
                assert isinstance(positive, list)
                fresh = cast('list[EVar | SVar]', stack.pop())
                assert isinstance(fresh, list)
                stack.append(MetaVar(name, tuple(fresh), tuple(positive), tuple(negative), tuple(application_context)))

            case Instruction.Prop1:
                phi0 = MetaVar(0, (), (), (), ())
                phi1 = MetaVar(1, (), (), (), ())
                stack.append(Proved(Implication(phi0, Implication(phi1, phi0))))
            case Instruction.Prop2:
                phi0 = MetaVar(0, (), (), (), ())
                phi1 = MetaVar(1, (), (), (), ())
                phi2 = MetaVar(2, (), (), (), ())
                stack.append(
                    Proved(
                        Implication(
                            Implication(phi0, Implication(phi1, phi2)),
                            Implication(Implication(phi0, phi1), Implication(phi0, phi2)),
                        )
                    )
                )

            case Instruction.InstantiateSchema:
                plug = stack.pop()
                assert isinstance(plug, Pattern)
                var = stack.pop()
                assert isinstance(var, MetaVar)
                metatheorem = stack.pop()
                assert isinstance(metatheorem, Proved), metatheorem
                stack.append(metatheorem.instantiate(var, plug))

            case Instruction.ModusPonens:
                phi_implies_psi = stack.pop()
                assert isinstance(phi_implies_psi, Proved), phi_implies_psi
                assert isinstance(phi_implies_psi.pattern, Implication), phi_implies_psi

                phi = stack.pop()
                assert isinstance(phi, Proved), phi

                assert phi.pattern == phi_implies_psi.pattern.left, (phi.pattern, phi_implies_psi.pattern.left)
                stack.append(Proved(phi_implies_psi.pattern.right))

            case Instruction.Save:
                assert isinstance(stack[-1], (Pattern, Proved))
                memory.append(stack[-1])
            case Instruction.Load:
                index = next(proof)
                stack.append(memory[index])

            case _:
                raise AssertionError('Unknown Instruction: %s' % instr)


def verify(gamma: Iterator[int], proof: Iterator[int]) -> tuple[Stack, Memory, Journal]:
    """Reads assumptions, proof, and emits a journal"""
    stack: Stack = []
    memory: Memory = []
    journal: Journal = []

    # TODO: Assert that no instructions use proof rules
    execute_instructions(gamma, stack, memory, journal)
    assert journal == [], 'Cannot publish from input.'
    memory = []
    for item in stack:
        assert isinstance(item, Pattern)
        memory.append(Proved(item))
    stack = []
    execute_instructions(proof, stack, memory, journal)
    return (stack, memory, journal)


# ----------------------------------------------------------------------------
# --------------------------- Testing Harness --------------------------------
# ----------------------------------------------------------------------------


def test_construct_phi_implies_phi() -> None:
    # fmt: off
    proof : list[int] = [
              int(Instruction.List), 0, # Fresh
              int(Instruction.List), 0, # Positive
              int(Instruction.List), 0, # Negative
              int(Instruction.List), 0, # Context
              int(Instruction.MetaVar), 0, # Stack: Phi
              int(Instruction.Save),    # @ 0
              int(Instruction.Load), 0, # Phi ; Phi
              int(Instruction.Implication), # Phi -> Phi
            ]
    # fmt: on
    phi = MetaVar(0, (), (), (), ())
    stack, memory, journal = verify(iter([]), iter(proof[0:10]))
    assert stack == [phi], stack
    stack, memory, journal = verify(iter([]), iter(proof))
    assert stack == [Implication(phi, phi)], stack


def test_prove_phi_implies_phi() -> None:
    # fmt: off
    proof : list[int] = [
              int(Instruction.Prop1),               # (p1: phi0 -> (phi1 -> phi0))

              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.MetaVar), 1,          # Stack: p1 ; phi1
              int(Instruction.Save),

              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.MetaVar), 0,          # Stack: p1 ; phi1 ; phi0
              int(Instruction.Save),

              int(Instruction.InstantiateSchema),   # Stack: (p2: phi0 -> (phi0 -> phi0))

              int(Instruction.Prop1),               # Stack: p2 ; p1
              int(Instruction.Load), 0,
              int(Instruction.Load), 1,
              int(Instruction.Load), 1,
              int(Instruction.Implication),         # Stack: p2 ; p1 ; phi1; phi0 -> phi0
              int(Instruction.Save),

              int(Instruction.InstantiateSchema),   # Stack: p2 ; (p3: phi0 -> (phi0 -> phi0) -> phi0)

              int(Instruction.Prop2),
              int(Instruction.Load), 0,
              int(Instruction.Load), 2,
              int(Instruction.InstantiateSchema),
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.List), 0,
              int(Instruction.MetaVar), 2,
              int(Instruction.Load), 1,
              int(Instruction.InstantiateSchema),


              int(Instruction.ModusPonens),
              int(Instruction.ModusPonens),         # Stack: phi0 -> phi0

              int(Instruction.Publish),
            ]
    # fmt: on
    phi0 = MetaVar(0, (), (), (), ())
    stack, memory, journal = verify(iter([]), iter(proof[0:55]))
    assert stack == [Proved(Implication(phi0, phi0))], stack


test_construct_phi_implies_phi()
test_prove_phi_implies_phi()
