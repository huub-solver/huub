%-------------%
% Annotations
%-------------%

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the edge finding propagation algorithm for the constraint. */
annotation edge_finding;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the not-last propagation algorithm for the constraint. */
annotation not_last;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the detectable precedence propagation algorithm for the constraint. */
annotation detectable_precedence;

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub enables the `check` propagation algorithm. If any circuit annotation is present, unannotated algorithms are disabled. */
annotation circuit_check;

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub enables the `prevent` propagation algorithm. If any circuit annotation is present, unannotated algorithms are disabled. */
annotation circuit_prevent;

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub enables the `scc` propagation algorithm. If any circuit annotation is present, unannotated algorithms are disabled. */
annotation circuit_scc;
