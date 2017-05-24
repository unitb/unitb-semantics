

Todo

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
	* models
	  * in nondet, push the reference to liveness out of transient
	* refinement
	  * ~~schedules~~
	  * ~~simulation~~
	  * ~~use `unless` `except`~~
	  * ~~splitting / merging~~
	  * data refinement
		  * based on observation function
		  * based on ghost state
		  * if we prove `p ↦ q in ma`, define what `p ↦ q in mc`, if
            mc is a data refinement
	  * reusing liveness properties
    * examples
	  * advisors
	  * train station
	  * lock free algorithm
	* shared variable decomposition
	* multiple coarse schedules
	* spontaneous events
	* state hiding
	* state variables

# sub projects #

	* verifier
	    * typed variables
	    * well-definedness
		* defunctionalization of sequents
	* pseudo code
	* Event-B liveness semantics

# cleanup #

    * ~~unity.temporal has hence_map, ex_map, init_map. rename them~~
