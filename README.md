# Eileen

This project is an implementation for some of the data structures of [Iris](https://iris-project.org) in Lean.
While the ultimate goal of the project is to support [lean-iris](https://github.com/leanprover-community/iris-lean) with a fully-fledged Iris implementation, the current target is to mechanize enough of the foundations to instansiate the frontend with ``upred``. 

## Blog posts:
- [Eileen: A plan for Iris in Lean](https://www.markusde.ca/pages/eileen.html)
- [What does iris-lean do?](https://www.markusde.ca/pages/iris_lean.html)

## Status:
The main mechanized results so far:
- Semi-bundled hierarchy for (C)OFE
	- Nonexpansive and contractive maps
- OFE instances:
	- OFE on (bundled) nonexpansive maps
	- discreteO, laterO, leibnizO, prodO
- Bundled (C)OFE:
	- The category of (C)OFE and nonexpansive maps
	- A definition for oFunctor
- Fixpoint of contractive maps

Future steps are described in _Eileen: A plan for Iris in Lean_. 
