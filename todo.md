

## Todo ##

    * tactic for monotonicity in predicate calculus
    * ~~reduce soundness of leads-to properties to assumptions about transient~~
	* ~~prove soundness of unitb.models.sched~~
	* prove that unitb.models.sched are inhabited
	* ~~in unitb.models.sched, give a rule that relies only on predicate
      calculus and UNITY logic~~
	* study model where the invariant is encoded in the state space
	* generalize transient_rule (from unity.models.nondet) and put in
      type class so that it becomes a requirement that other models
      can subscribe to
	* refinement
	  * ~~schedules~~
	  * ~~simulation~~
	  * use `unless` `except`
	  * splitting / merging
	  * data refinement
	  * reusing liveness properties
	* shared variable decomposition
	* spontaneous events
	* state hiding
	* pseudo code
	* state variables
	* multiple coarse schedules

# cleanup #

    * unity.temporal has hence_map, ex_map, init_map. rename them
