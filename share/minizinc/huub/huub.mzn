%-------------%
% Annotations
%-------------%

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub uses the no-cycle propagation algorithm for the constraint. */
annotation circuit_no_cycle;

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub uses the strongly-connected-component propagation algorithm for the constraint. */
annotation circuit_scc;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the edge finding propagation algorithm for the constraint. */
annotation edge_finding;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the not-last propagation algorithm for the constraint. */
annotation not_last;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the detectable precedence propagation algorithm for the constraint. */
annotation detectable_precedence;
