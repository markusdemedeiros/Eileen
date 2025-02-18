# Eileen

> [!IMPORTANT]  
> Work on [lean-iris](https://github.com/leanprover-community/iris-lean) has restarted! To consolidate the effort, this project is no longer active. Interested contributors should work on lean-iris instead. 


This project is an implementation for some of the data structures of [Iris](https://iris-project.org) in Lean.
While the ultimate goal of the project is to support [lean-iris](https://github.com/leanprover-community/iris-lean) with a fully-fledged Iris implementation, the current target is to mechanize enough of the foundations to instantiate the frontend with ``upred``. 

**This project is a work in progress**

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
        - The category OFE is cartesian closed
	- A definition for oFunctor
- Fixpoint of contractive maps

Future steps are described in _Eileen: A plan for Iris in Lean_. 

## Contributing:

Do not run ``lake update`` without a PR. 
This project tracks the ``lake-manifest`` file in order to pin the mathlib version.

PR's regarding code improvements, CI, and compliance with the Mathlib style guide are very welcome!
If you would like to contribute to the main porting effort please get in touch with me at ``@markusdemedeiros`` on the Lean Zulip, or by email, in order to avoid redundant work. 
