
.PHONY: all root logic models refinement syntax clean lines

LEAN_OPT = 

all:
	lean $(LEAN_OPT) --make > errors.txt

root: logic models refinement

logic: unity/logic.olean unity/refinement.olean

models: unity/models/nondet.olean unity/models/det.olean unity/models/simple.olean unity/models/sched.olean

refinement: unity/models/refinement/resched_data_ref.olean unity/models/refinement/split.olean unity/models/refinement/split_merge.olean unity/models/refinement/reschedule.olean

syntax: unity/syntax/exists.olean unity/syntax/simple.olean

%.olean: %.lean $(shell lean $< --deps)
	lean $(LEAN_OPT) $<

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `/usr/bin/find . -name "*.lean"`
