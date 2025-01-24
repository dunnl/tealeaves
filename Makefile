SHELL = bash
COQ_MAKEFILE  := Makefile.coq
COQ_PROJ     := _CoqProject
COQ_VS       := $(shell find Tealeaves/ -name "*.v")
RM_ARTIFACTS := extra/remove_artifacts.sh
export COQ_MAKEFILE

all: coqdocs

# Generate Makefile.coq from _CoqProject and .v files
# $(COQ_VS) forces regeneration whenever a .v has a more recent timestamp
# $(COQ_PROJ) forces regeneration whenever a _CoqProject has a more recent timestamp
$(COQ_MAKEFILE): $(COQ_PROJ) $(COQ_VS)
	@echo "Generating Makefile.coq" #with $(COQ_VS)"
	coq_makefile -f $(COQ_PROJ) -o $@

$(COQ_VS):
	@echo "This statement shouldn't be reached, but was reached via $@"

# html: Generate Coqdocs
# gallinahtml: Generate Coqdocs without proofs
# coqdocs: Generate HTML Coqdocs with CoqdocJS
# alectryon: Generate HTML with Alectryon
html gallinahtml coqdocs alectryon alectryon-toc alectryon-clean: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) $@

# Any target not matched above will be passed to Makefile.coq
%: $(COQ_MAKEFILE) force
	@echo "'%' pattern target running for target \"$@\""
	$(MAKE) -f $(COQ_MAKEFILE) $@

# Supress Makefile's auto-rebuilding target
# # https://stackoverflow.com/questions/67251937/makefile-match-anything-rule-picks-up-makefile-target
Makefile: ;

# Placeholder if we wanted to generate _CoqProject
$(COQ_PROJ): ;

install-examples:
	cp html-examples/* ${out} -r

# The last command requires GNU find and deletes empty directories
# under Tealeaves/
clean: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) $@
	rm -f $(COQ_MAKEFILE)
	$(RM_ARTIFACTS)
	find Tealeaves/ . -type d -empty -delete

clean-html:
	rm -fr html

clean-all: clean clean-html

# Warning: this interactively destroys all files not under version
# control
clean-repo: clean
	git clean -xdi -e Makefile.coq.conf -e Makefile.coq.local -e ".*"

force: ;
.PHONY: clean all force clean-repo examples-html install-examples
