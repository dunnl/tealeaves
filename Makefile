COQDOC_EXTRA_DIR:=extra/CoqdocJS
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(COQDOC_EXTRA_DIR)/header.html \
  --with-footer $(COQDOC_EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
COQ_VS := $(shell find Tealeaves/ -name "*.v")
RM_ARTIFACTS := find . -type f -regextype posix-egrep -iregex '.*\.(vo|vos|vok|aux|glob|cache)$$' -delete

all: html

# The last command requires GNU find and deletes empty directories
# under Tealeaves/
clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)
	rm -fr html
	$(RM_ARTIFACTS)
	find Tealeaves/ . -type d -empty -delete

# Warning: this destroys all files not under version control
clean-repo: clean
	git clean -xi -e Makefile.coq.conf

html: $(COQMAKEFILE) $(COQ_VS)
	rm -fr html
	$(MAKE) -f $(COQMAKEFILE) $@
	cp $(COQDOC_EXTRA_DIR)/resources/* html

#alectryon: $(COQMAKEFILE) $(COQMF_VFILES)
#	rm -fr html-alectryon
#	alectryon --output-directory html-alectryon $(COQMF_VFILES)

# Generate Makefile.coq from _CoqProject and .v files
# A "force" dependency regenerates the Makefile every time
# $(COQ_VS) forces regeneration whenever a .v has a more recent timestamp
# $(COQ_PROJ) forces regeneration whenever a _CoqProject has a more recent timestamp
$(COQMAKEFILE): $(COQ_PROJ) $(COQ_VS)
	@echo "Generating Makefile.coq" #with $(COQ_VS)"
	coq_makefile -f $(COQ_PROJ) -o $@

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

force: ;
.PHONY: clean all force showvars clean-repo
