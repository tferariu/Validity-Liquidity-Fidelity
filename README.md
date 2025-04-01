# agda2plinth: Formal verification of Cardano smart contracts in Agda
[![CI](https://github.com/tferariu/agda2plinth/workflows/CI/badge.svg)](https://github.com/tferariu/agda2plinth/actions) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.???.svg)](https://doi.org/10.5281/zenodo.???)

A prototype verification methodology, whereas Plutus contracts are modeled and formally verified in Agda,
and subsequently compiled to Plinth via the agda2hs transpiler.

# Versions

- agda2hs: v1.3 (uses Agda v2.7.0.1 as a library)
- agda-stdlib: v2.2

# Setup instructions

- To just typecheck the Agda files: `make typecheck`
- To compile the Agda files to Haskell (under the dist/ directory): `make compile`
