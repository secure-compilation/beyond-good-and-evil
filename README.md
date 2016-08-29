## Beyond Good and Evil: Formalizing the Security Guarantees of Compartmentalizing Compilation

This repository contains auxiliary materials for the following paper:

- Yannis Juglaret, Cătălin Hriţcu, Arthur Azevedo de Amorim, Boris Eng, and Benjamin C. Pierce.
  Beyond Good and Evil: Formalizing the Security Guarantees of Compartmentalizing Compilation.
  In 29th IEEE Symposium on Computer Security Foundations (CSF), pages 45–60.
  IEEE Computer Society Press, July 2016. Technical report https://arxiv.org/abs/1602.04503

In particular, these materials include:
- `sfa-to-scc-coq`: a Coq proof for Theorem 3.4 showing that structured full abstraction
  instantiated to components implies Secure Compartmentalizing Compilation (SCC)
- `simple-instance.org`and `simple-instance-coq`:
  technical details and proofs for the SCC instance from Section 4, both on paper and in Coq
- `trace-mapping-testing`: a trace mapping algorithm in OCaml using property-based testing
  to check the Definability assumption from Section 4
