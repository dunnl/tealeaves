SHELL = bash
COQDOC_EXTRA_DIR := extra/CoqdocJS
COQDOCEXTRAFLAGS := \
  --toc-depth 2 \
  --index indexpage \
  --no-lib-name \
  --parse-comments \
  --with-header $(COQDOC_EXTRA_DIR)/header.html \
  --with-footer $(COQDOC_EXTRA_DIR)/footer.html
export COQDOCEXTRAFLAGS
COQMAKEFILE  := Makefile.coq
COQ_PROJ     := _CoqProject
COQ_VS       := $(shell find Tealeaves/ -name "*.v")
RM_ARTIFACTS := extra/remove_artifacts.sh
CLEANUP_CSS  := extra/format_css.sh
HIDE =
export HIDE
all: html

# The last command requires GNU find and deletes empty directories
# under Tealeaves/
clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)
	$(RM_ARTIFACTS)
	find Tealeaves/ . -type d -empty -delete

clean-html:
	rm -fr html

clean-all: clean clean-html

# Warning: this interactively destroys all files not under version
# control
clean-repo: clean
	git clean -xdi -e Makefile.coq.conf -e Makefile.coq.local -e ".*"

# Generate Makefile.coq from _CoqProject and .v files
# A "force" dependency regenerates the Makefile every time
# $(COQ_VS) forces regeneration whenever a .v has a more recent timestamp
# $(COQ_PROJ) forces regeneration whenever a _CoqProject has a more recent timestamp
$(COQMAKEFILE): $(COQ_PROJ) $(COQ_VS)
	@echo "Generating Makefile.coq" #with $(COQ_VS)"
	coq_makefile -f $(COQ_PROJ) -o $@

build: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $@

# Generate nicely formatted HTML with CoqdocJS
html: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $@
	cp $(COQDOC_EXTRA_DIR)/resources/* html

# Any target not matched above will be passed to Makefile.coq
%: $(COQMAKEFILE) force
	@echo "'%' pattern target running for target \"$@\""
	$(MAKE) -f $(COQMAKEFILE) $@

# Supress Makefile's auto-rebuilding target
# # https://stackoverflow.com/questions/67251937/makefile-match-anything-rule-picks-up-makefile-target
Makefile: ;

# Placeholder if we wanted generate _CoqProject
$(COQ_PROJ): ;

# Don't run any action for matched files
$(COQ_VS): #force
	@echo "This statement shouldn't be reached, but was reached via $@"

showvars:
	@echo $(COQ_VS)

examples-clean:
	rm -Rf html-examples/

examples-html:
	mkdir -p html-examples/STLC
	mkdir -p html-examples/SystemF
	alectryon Tealeaves/Backends/LN/LN.v                  --output-directory ./html-examples -o ./html-examples/LN/LN.html
	alectryon Tealeaves/Examples/STLC/Syntax.v            --output-directory ./html-examples -o ./html-examples/STLC/Syntax.html
	alectryon Tealeaves/Examples/STLC/SyntaxCategorical.v --output-directory ./html-examples -o ./html-examples/STLC/SyntaxCategorical.html
	alectryon Tealeaves/Examples/STLC/TypeSoundness.v     --output-directory ./html-examples -o ./html-examples/STLC/TypeSoundness.html
	#alectryon Tealeaves/Examples/SystemF/Syntax.v         --output-directory ./html-examples -o ./html-examples/SystemF/Syntax.html
	./$(CLEANUP_CSS)

examples-install:
	cp html-examples/* ${out} -r

force: ;
.PHONY: clean all force showvars clean-repo examples-html examples-clean examples-install
