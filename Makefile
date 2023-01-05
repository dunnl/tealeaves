EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v)

all: html

clean: $(COQMAKEFILE)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html

#alectryon: $(COQMAKEFILE) $(COQMF_VFILES)
#	rm -fr html-alectryon
#	alectryon --output-directory html-alectryon $(COQMF_VFILES)

$(COQMAKEFILE): $(COQ_PROJ) $(VS)
	coq_makefile -f $(COQ_PROJ) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: clean all force
