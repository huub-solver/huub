%-------------%
% Annotations
%-------------%

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub uses the no-cycle propagation algorithm for the constraint. */
annotation circuit_no_cycle;

/** @group huub.annotations When used on a circuit or subcircuit constraint, Huub uses the strongly-connected-component propagation algorithm for the constraint. */
annotation circuit_scc;

/** @group huub.annotations When used on a cumulative constraint, Huub uses the time-table-edge-finding propagation algorithm for the constraint. */
annotation cumulative_edge_finding;

/** @group huub.annotations When used on a cumulative constraint, Huub uses the energy overload checking algorithm for the constraint. */
annotation cumulative_energy_overload;

/** @group huub.annotations When used on a cumulative constraint, Huub additionally uses the opportunistic extended-edge-finding rules for the constraint. */
annotation cumulative_opportunistic_edge_finding;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the edge finding propagation algorithm for the constraint. */
annotation disjunctive_edge_finding;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the not-last propagation algorithm for the constraint. */
annotation disjunctive_not_last;

/** @group huub.annotations When used on a disjunctive constraint, Huub uses the detectable precedence propagation algorithm for the constraint. */
annotation disjunctive_detectable_precedence;
