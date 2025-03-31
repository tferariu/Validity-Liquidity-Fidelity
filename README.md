# agda2plinth

A prototype verification methodology, whereas Plutus contracts are modeled and formally verified in Agda,
and subsequently compiled to Plinth via the agda2hs transpiler.

# Versions

- agda: 2.6.4.1
- agda2hs: between v1.2 & v1.3, commit f5ac455
- agda-stdlib: v1.7.2

# Setup instructions

1. Typecheck files using `agda`
2. Generate Haskell code using `agda2hs`
