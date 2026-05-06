# Researching Huub

If you use Huub in your research or development, please cite the software:

```bibtex
@software{Huub,
  author = {Dekker, Jip J. and Stuckey, Peter J. and Zhong, Allen Z.},
  title = {Huub},
  license = {MPL-2.0},
  url = {https://huub.solutions},
  doi = {10.5281/zenodo.15591852},
}
```

## Related research

**Towards Modern and Modular SAT for LCG**
*Design of Huub using IPASIR-UP*

This paper describes the design of Huub and how it uses the IPASIR-UP interface to build a modern Lazy Clause Generation solver.
It shows how using a pluggable SAT backend through IPASIR-UP enables better solver engineering, allows for modularity without sacrificing competitiveness, and makes it possible to take advantage of advances in SAT solving technology.

DOI: [10.4230/LIPIcs.CP.2025.42](https://doi.org/10.4230/LIPIcs.CP.2025.42)

**Satisfiability Modulo User Propagators**
*IPASIR-UP journal paper*

Huub is built on the IPASIR-UP interface, which fundamentally changes how constraint programming and SAT solving can be integrated.
Rather than encoding everything into clauses upfront, IPASIR-UP allows external components to dynamically participate in the SAT solver's search process.
This is what makes Lazy Clause Generation possible: the constraint propagation engine can lazily create clauses as needed, while the SAT solver's learning and conflict analysis mechanisms provide the reasoning power.
IPASIR-UP was designed specifically to support sophisticated solving architectures like Huub, where the embedding system has domain knowledge that can guide and improve the search.

DOI: [10.1613/jair.1.16163](https://doi.org/10.1613/jair.1.16163)
