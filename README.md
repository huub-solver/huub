# Huub

<p align="center">
  <img
    src="https://huub.solutions/favicon.svg"
    alt="Huub logo"
    height="350px">
</p>

Huub is an efficient library for developing constraint-based decision or optimization systems and applications with learning capabilities.
It combines the modelling strengths of constraint programming (CP) with the learning and proof machinery of Boolean satisfiability (SAT) solving.

Huub is **reliable**: it is well-tested, performs state-of-the-art preprocessing before search begins, and is implemented in Rust for a safer and more dependable solver core.
It is **performant**: it combines strong propagation with modern solving techniques to deliver competitive performance on demanding decision problems.
And it is **extensible**: you can add your own propagators, branchers, and even replace the underlying SAT solver, so it can be shaped around your specific needs.

## Links

- [Website](https://huub.solutions)
- [crates.io](https://crates.io/crates/huub)
- [docs.rs](https://docs.rs/huub/latest/huub/)
- [Discord](https://discord.gg/62xajSNBAR)

## Thanks

Thanks to our [contributors](https://huub.solutions/misc/contributors.html) and [funding partners](https://huub.solutions/misc/funding.html).

## Citing Huub

If you want to cite Huub please use our general software citation, in addition to any citation to a specific version or paper:

```bibtex
@software{Huub,
  author = {Dekker, Jip J. and Stuckey, Peter J. and Zhong, Allen Z.},
  title = {Huub},
  license = {MPL-2.0},
  url = {https://huub.solutions},
  doi = {10.5281/zenodo.15591852},
}
```
