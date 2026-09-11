Proposed road map structure:


# Roadmap: topic
## 1. Goal: eventually, what is your goal? Why is it important?

## 2. Completion criterion: 
what is the theorem you are viewing as a milestone? 
Note the theorem could be big and could be small.

## 3. Scope
list the things inside this design doc 
## 4. Out of scope
what will not be covered
## 5. Mathematical model

what is the realtionship between math informally and the thing formally you wanna build

## 6. Design decisions and conventions
Lets fix some design choices, choose the choice related to you goal
- carrier types: what is the type of the object you wanna study
- namespace
- parameter order: what are the orders of the object you wanna approach
- totalization/boundary behavior: any potential junk value?
- composition convention
- typeclass assumptions
- finite/infinite conventions


## 7. Existing Mathlib and Statlib foundations

List which PR/file you might be mainly use; also state what willl not be use 

## 8. Proposed file organization

```text
Project/Area/Basic.lean
Project/Area/Operations.lean
Project/Area/MainTheorem.lean
``` 
Any comments are welcome! This is just a proposed design doc — the goal is to reduce communication overhead and serve as a reference for anyone joining the project later.
