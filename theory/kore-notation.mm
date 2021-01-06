$[ theory/kore.mm $]

${
    notation-kore-valid.0 $e #Notation ph0 ph2 $.
    notation-kore-valid.1 $e #Notation ph1 ph3 $.
    notation-kore-valid $p #Notation ( \kore-valid ph0 ph1 ) ( \kore-valid ph2 ph3 ) $= ph0-is-pattern ph1-is-pattern kore-valid-is-pattern ph1-is-pattern ph0-is-pattern kore-top-is-pattern eq-is-pattern ph2-is-pattern ph3-is-pattern kore-valid-is-pattern ph0-is-pattern ph1-is-pattern kore-valid-is-sugar ph2-is-pattern ph3-is-pattern kore-valid-is-pattern ph1-is-pattern ph0-is-pattern kore-top-is-pattern eq-is-pattern ph2-is-pattern ph3-is-pattern kore-valid-is-pattern ph3-is-pattern ph2-is-pattern kore-top-is-pattern eq-is-pattern ph1-is-pattern ph0-is-pattern kore-top-is-pattern eq-is-pattern ph2-is-pattern ph3-is-pattern kore-valid-is-sugar ph1-is-pattern ph0-is-pattern kore-top-is-pattern eq-is-pattern ph3-is-pattern ph2-is-pattern kore-top-is-pattern eq-is-pattern ph1-is-pattern ph0-is-pattern kore-top-is-pattern ph3-is-pattern ph2-is-pattern kore-top-is-pattern notation-kore-valid.1 ph0-is-pattern kore-top-is-pattern ph0-is-pattern inh-is-pattern ph2-is-pattern kore-top-is-pattern ph0-is-pattern kore-top-is-sugar ph2-is-pattern kore-top-is-pattern ph0-is-pattern inh-is-pattern ph2-is-pattern kore-top-is-pattern ph2-is-pattern inh-is-pattern ph0-is-pattern inh-is-pattern ph2-is-pattern kore-top-is-sugar ph0-is-pattern inh-is-pattern ph2-is-pattern inh-is-pattern ph0-is-pattern ph2-is-pattern notation-kore-valid.0 notation-inh notation-symmetry notation-transitivity notation-symmetry notation-transitivity notation-eq notation-symmetry notation-transitivity notation-symmetry notation-transitivity $.
$}

${
    notation-kore-next.0 $e #Notation ph0 ph2 $.
    notation-kore-next.1 $e #Notation ph1 ph3 $.
    notation-kore-next $p #Notation ( \kore-next ph0 ph1 ) ( \kore-next ph2 ph3 ) $= ph0-is-pattern ph1-is-pattern kore-next-is-pattern kore-next-is-symbol symbol-is-pattern ph1-is-pattern app-is-pattern ph2-is-pattern ph3-is-pattern kore-next-is-pattern ph0-is-pattern ph1-is-pattern kore-next-is-sugar ph2-is-pattern ph3-is-pattern kore-next-is-pattern kore-next-is-symbol symbol-is-pattern ph1-is-pattern app-is-pattern ph2-is-pattern ph3-is-pattern kore-next-is-pattern kore-next-is-symbol symbol-is-pattern ph3-is-pattern app-is-pattern kore-next-is-symbol symbol-is-pattern ph1-is-pattern app-is-pattern ph2-is-pattern ph3-is-pattern kore-next-is-sugar kore-next-is-symbol symbol-is-pattern ph1-is-pattern app-is-pattern kore-next-is-symbol symbol-is-pattern ph3-is-pattern app-is-pattern kore-next-is-symbol symbol-is-pattern ph1-is-pattern kore-next-is-symbol symbol-is-pattern ph3-is-pattern kore-next-is-symbol symbol-is-pattern notation-reflexivity notation-kore-next.1 notation-app notation-symmetry notation-transitivity notation-symmetry notation-transitivity $.
$}

${
    notation-kore-or.0 $e #Notation ph0 ph3 $.
    notation-kore-or.1 $e #Notation ph1 ph4 $.
    notation-kore-or.2 $e #Notation ph2 ph5 $.
    notation-kore-or $p #Notation ( \kore-or ph0 ph1 ph2 ) ( \kore-or ph3 ph4 ph5 ) $= ph0-is-pattern ph1-is-pattern ph2-is-pattern kore-or-is-pattern ph1-is-pattern ph2-is-pattern or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-or-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern kore-or-is-sugar ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-or-is-pattern ph1-is-pattern ph2-is-pattern or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-or-is-pattern ph4-is-pattern ph5-is-pattern or-is-pattern ph1-is-pattern ph2-is-pattern or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-or-is-sugar ph1-is-pattern ph2-is-pattern or-is-pattern ph4-is-pattern ph5-is-pattern or-is-pattern ph1-is-pattern ph2-is-pattern ph4-is-pattern ph5-is-pattern notation-kore-or.1 notation-kore-or.2 notation-or notation-symmetry notation-transitivity notation-symmetry notation-transitivity $.
$}

${
    notation-kore-implies.0 $e #Notation ph0 ph3 $.
    notation-kore-implies.1 $e #Notation ph1 ph4 $.
    notation-kore-implies.2 $e #Notation ph2 ph5 $.
    notation-kore-implies $p #Notation ( \kore-implies ph0 ph1 ph2 ) ( \kore-implies ph3 ph4 ph5 ) $= ph0-is-pattern ph1-is-pattern ph2-is-pattern kore-implies-is-pattern ph0-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph2-is-pattern kore-or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-implies-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern kore-implies-is-sugar ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-implies-is-pattern ph0-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph2-is-pattern kore-or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-implies-is-pattern ph3-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph5-is-pattern kore-or-is-pattern ph0-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph2-is-pattern kore-or-is-pattern ph3-is-pattern ph4-is-pattern ph5-is-pattern kore-implies-is-sugar ph0-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph2-is-pattern kore-or-is-pattern ph3-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph5-is-pattern kore-or-is-pattern ph0-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph2-is-pattern ph3-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph5-is-pattern notation-kore-implies.0 ph0-is-pattern ph1-is-pattern kore-not-is-pattern ph1-is-pattern not-is-pattern ph0-is-pattern kore-top-is-pattern and-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph0-is-pattern ph1-is-pattern kore-not-is-sugar ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph1-is-pattern not-is-pattern ph0-is-pattern kore-top-is-pattern and-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-pattern ph4-is-pattern not-is-pattern ph3-is-pattern kore-top-is-pattern and-is-pattern ph1-is-pattern not-is-pattern ph0-is-pattern kore-top-is-pattern and-is-pattern ph3-is-pattern ph4-is-pattern kore-not-is-sugar ph1-is-pattern not-is-pattern ph0-is-pattern kore-top-is-pattern and-is-pattern ph4-is-pattern not-is-pattern ph3-is-pattern kore-top-is-pattern and-is-pattern ph1-is-pattern not-is-pattern ph0-is-pattern kore-top-is-pattern ph4-is-pattern not-is-pattern ph3-is-pattern kore-top-is-pattern ph1-is-pattern ph4-is-pattern notation-kore-implies.1 notation-not ph0-is-pattern kore-top-is-pattern ph0-is-pattern inh-is-pattern ph3-is-pattern kore-top-is-pattern ph0-is-pattern kore-top-is-sugar ph3-is-pattern kore-top-is-pattern ph0-is-pattern inh-is-pattern ph3-is-pattern kore-top-is-pattern ph3-is-pattern inh-is-pattern ph0-is-pattern inh-is-pattern ph3-is-pattern kore-top-is-sugar ph0-is-pattern inh-is-pattern ph3-is-pattern inh-is-pattern ph0-is-pattern ph3-is-pattern notation-kore-implies.0 notation-inh notation-symmetry notation-transitivity notation-symmetry notation-transitivity notation-and notation-symmetry notation-transitivity notation-symmetry notation-transitivity notation-kore-implies.2 notation-kore-or notation-symmetry notation-transitivity notation-symmetry notation-transitivity $.
$}