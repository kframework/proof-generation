from typing import TextIO, Optional, Set, Union, Dict, Tuple, Any

from urllib.parse import quote_plus

from ml.kore import ast as kore
from ml.kore.ast import KoreVisitor
from ml.kore.utils import KoreUtils

from ml.metamath import ast as mm
from ml.metamath.utils import MetamathUtils


class KorePatternEncoder(KoreVisitor[kore.BaseAST[Any], mm.Term]):
    """
    Encode a kore pattern as a Term and collect all metavariables
    and constant symbols
    """

    TOP = "\\kore-top"
    BOTTOM = "\\kore-bottom"
    NOT = "\\kore-not"
    AND = "\\kore-and"
    OR = "\\kore-or"
    IMPLIES = "\\kore-implies"
    IFF = "\\kore-iff"
    CEIL = "\\kore-ceil"
    FLOOR = "\\kore-floor"
    EQUALS = "\\kore-equals"
    IN = "\\kore-in"
    REWRITES = "\\kore-rewrites"
    REWRITES_STAR = "\\kore-rewrites-star"
    DV = "\\kore-dv"
    IS_SORT = "\\kore-is-sort"
    STRING = "\\kore-string"

    FORALL = "\\kore-forall"
    EXISTS = "\\kore-exists"
    FORALL_SORT = "\\kore-forall-sort"
    VALID = "\\kore-valid"

    LOGIC_CONSTRUCT_MAP = {
        kore.MLPattern.TOP: TOP,
        kore.MLPattern.BOTTOM: BOTTOM,
        kore.MLPattern.NOT: NOT,
        kore.MLPattern.AND: AND,
        kore.MLPattern.OR: OR,
        kore.MLPattern.IMPLIES: IMPLIES,
        kore.MLPattern.IFF: IFF,
        kore.MLPattern.CEIL: CEIL,
        kore.MLPattern.FLOOR: FLOOR,
        kore.MLPattern.EQUALS: EQUALS,
        kore.MLPattern.IN: IN,
        kore.MLPattern.REWRITES: REWRITES,
        kore.MLPattern.REWRITES_STAR: REWRITES_STAR,
        kore.MLPattern.DV: DV,
        kore.MLPattern.FORALL: FORALL,
        kore.MLPattern.EXISTS: EXISTS,
    }

    @staticmethod
    def encode_symbol(symbol: Union[kore.SymbolInstance, str]) -> str:
        if isinstance(symbol, str):
            symbol_str = symbol
        else:
            symbol_str = symbol.get_symbol_name()

        if symbol_str == "inj":
            return "\\kore-inj"

        return "\\kore-symbol-" + symbol_str

    @staticmethod
    def encode_sort(sort: Union[kore.SortInstance, str]) -> str:
        if isinstance(sort, str):
            sort_id = sort
        else:
            sort_id = sort.get_sort_id()

        return "\\kore-sort-" + sort_id

    @staticmethod
    def encode_string_literal(literal: kore.StringLiteral) -> str:
        return '"' + quote_plus(literal.content) + '"'

    @staticmethod
    def encode_logical_construct(construct: str) -> str:
        return KorePatternEncoder.LOGIC_CONSTRUCT_MAP[construct]

    @staticmethod
    def encode_variable(var: kore.Variable) -> str:
        return "kore-element-var-" + var.name

    @staticmethod
    def encode_sort_variable(var: kore.SortVariable) -> str:
        return "kore-sort-var-" + var.name

    def __init__(self) -> None:
        self.metavariables: Dict[str, str] = {}  # var -> typecode
        self.constant_symbols: Dict[str, int] = {}  # symbol -> arity
        self.domain_values: Set[Tuple[kore.SortInstance, kore.StringLiteral]] = set()  # set of (sort, string literal)

    def postvisit_axiom(self, axiom: kore.Axiom) -> mm.Term:
        body = self.visit(axiom.pattern)
        sort = KoreUtils.infer_sort(axiom.pattern)
        encoded_sort = self.visit(sort)

        body = mm.Application(KorePatternEncoder.VALID, (encoded_sort, body))

        premises = MetamathUtils.construct_top()

        free_vars = list(KoreUtils.get_free_variables(axiom))
        free_vars.sort(key=lambda var: var.name, reverse=True)

        # add sorting hypotheses for all free variables
        for var in free_vars:
            encoded_var = self.visit(var)
            encoded_sort = self.visit(var.sort)
            premises = MetamathUtils.construct_and(
                MetamathUtils.construct_in_sort(encoded_var, encoded_sort),
                premises,
            )

        # add sorting hypotheses for all sort variables
        for var in axiom.sort_variables[::-1]:
            encoded_var = self.visit(var)
            premises = MetamathUtils.construct_and(
                MetamathUtils.construct_in_sort(encoded_var, MetamathUtils.construct_sort()),
                premises,
            )

        return MetamathUtils.construct_imp(premises, body)

    def postvisit_sort_instance(self, sort_instance: kore.SortInstance) -> mm.Term:
        encoded = KorePatternEncoder.encode_sort(sort_instance)
        self.constant_symbols[encoded] = len(sort_instance.arguments)
        return mm.Application(encoded, tuple(self.visit(arg) for arg in sort_instance.arguments))

    def postvisit_sort_variable(self, sort_variable: kore.SortVariable) -> mm.Term:
        encoded_var = KorePatternEncoder.encode_sort_variable(sort_variable)
        self.metavariables[encoded_var] = "#ElementVariable"
        return mm.Metavariable(encoded_var)

    def postvisit_variable(self, var: kore.Variable) -> mm.Term:
        encoded_var = KorePatternEncoder.encode_variable(var)
        # assert not var.is_set_variable, f"set variables are not supported: {var}"
        self.metavariables[encoded_var] = "#ElementVariable" if not var.is_set_variable else "#SetVariable"
        return mm.Metavariable(encoded_var)

    def postvisit_string_literal(self, literal: kore.StringLiteral) -> mm.Term:
        encoded = KorePatternEncoder.encode_string_literal(literal)
        self.constant_symbols[encoded] = 0
        return mm.Application(encoded)

    def postvisit_application(self, application: kore.Application) -> mm.Term:
        constant_symbol = KorePatternEncoder.encode_symbol(application.symbol)
        self.constant_symbols[constant_symbol] = len(application.symbol.sort_arguments) + len(application.arguments)
        return mm.Application(
            constant_symbol,
            tuple(self.visit(sort_arg) for sort_arg in application.symbol.sort_arguments) +
            tuple(self.visit(arg) for arg in application.arguments),
        )

    def postvisit_ml_pattern(self, ml_pattern: kore.MLPattern) -> mm.Term:
        encoded_construct = KorePatternEncoder.encode_logical_construct(ml_pattern.construct)

        if (ml_pattern.construct == kore.MLPattern.FORALL or ml_pattern.construct == kore.MLPattern.EXISTS):
            var = ml_pattern.get_binding_variable()
            assert len(ml_pattern.arguments) == 2
            assert var is not None

            return mm.Application(
                encoded_construct,
                (
                    self.visit(var.sort),
                    self.visit(ml_pattern.sorts[0]),
                    self.visit(var),
                    self.visit(ml_pattern.arguments[1]),
                ),
            )

        else:
            if ml_pattern.construct == kore.MLPattern.DV:
                assert len(ml_pattern.sorts) == 1
                assert isinstance(ml_pattern.sorts[0], kore.SortInstance)
                assert isinstance(ml_pattern.arguments[0], kore.StringLiteral)
                self.domain_values.add((ml_pattern.sorts[0], ml_pattern.arguments[0]))

            return mm.Application(
                encoded_construct,
                tuple(self.visit(sort)
                      for sort in ml_pattern.sorts) + tuple(self.visit(arg) for arg in ml_pattern.arguments),
            )
