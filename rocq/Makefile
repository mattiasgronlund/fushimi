# Checks the proofs with Rocq 9.1, Flocq 4.2.2 and Gappa 1.6.0 (see README.md).

# Warnings are errors, like `-Dwarnings` for the Rust code.
COQEXTRAFLAGS := -w +default
export COQEXTRAFLAGS

# The recipes of this Makefile run under bash with `-euo pipefail`
# (.SHELLFLAGS takes GNU Make 3.82 or later), not under /bin/sh, which is
# dash on Debian and Ubuntu, and the dash of Debian 12 and Ubuntu 24.04 has
# no pipefail. A pipe then fails when any of its stages fails, not only when
# its last one does, and a recipe line stops at the first command that fails,
# unless the line tests that command's status, as `if` and `||` do. A pipe
# negated with `!` would pass when one of its stages fails, so none is.
# The recipes of RocqMakefile, which `proofs` runs, still run under /bin/sh,
# since make ignores SHELL in the environment and RocqMakefile sets none.
SHELL := bash
.SHELLFLAGS := -euo pipefail -c

# The axioms that the theorems may depend on: those of the real numbers in
# Stdlib, and excluded middle, which Flocq uses. Any other axiom, such as a
# proof left `Admitted`, fails the build.
AXIOMS := \
	ClassicalDedekindReals.sig_forall_dec \
	ClassicalDedekindReals.sig_not_dec \
	Classical_Prop.classic \
	FunctionalExtensionality.functional_extensionality_dep

all: assumptions examples

proofs: RocqMakefile
	$(MAKE) -f RocqMakefile

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

# `Print Assumptions` prints each axiom as `name : type`, with the type
# possibly continued on indented lines. This reads them from what Rocq
# prints on its standard output only, so it does not check the axioms that
# a `Print Assumptions` under `Redirect` writes to a file. For `examples`,
# Rocq also writes in Assumptions.glob the names of the theorems that
# Assumptions.v prints, and Assumptions.v writes the output of two
# `Search`es in MpfrSearch.out and MpfrSearchValid.out.
assumptions: proofs
	rm -f Assumptions.glob MpfrSearch.out MpfrSearchValid.out
	rocq compile $(COQEXTRAFLAGS) -output-directory . -R theories Fushimi \
		-dump-glob Assumptions.glob Assumptions.v \
		| sed -n 's/^\([^ ]*\) :.*/\1/p' | LC_ALL=C sort -u > Assumptions.out
	printf '%s\n' $(AXIOMS) | LC_ALL=C sort | diff -u - Assumptions.out

# IN_GLOB prints each name on its input whose last part, after its last `.`,
# is the <name> of an R line of Assumptions.glob, for `examples`. Rocq writes
# a line `R<start>:<end> <library> <module> <name> <kind>` there for each
# file that a `Require` of Assumptions.v names, with `<>` for <module> and
# <name>, and for each reference of Assumptions.v to a constant, a type or a
# constructor, such as the theorem that a `Print Assumptions` prints, with
# the last part of its full name as <name>, whatever name Assumptions.v
# uses. A reference to a module or a section, such as one that `Import`
# makes, gets a line with `<>` for <name>, and the `Valid` of `inside Valid`
# gets none. `NR == FNR` tells the lines of Assumptions.glob from those of
# the input only if Assumptions.glob is not empty, which `examples` tests
# first.
IN_GLOB := awk 'NR == FNR { if ($$1 ~ /^R[0-9]+:[0-9]+$$/ && $$4 != "<>") p[$$4]; next } \
	{ k = $$0; sub(/.*\./, "", k) } k in p' Assumptions.glob -

# STRIP prints each line of a Rocq file without its comments and strings.
# `examples` uses it only on theories/MpfrExamples.v. As in Rocq, comments
# nest, and a string, in code or in a comment, runs to the next `"`, so that
# the `(*` in `"(*"` opens no comment. Rocq writes a `"` in a string as `""`,
# which this reads as two strings, to the same effect. `d`, the depth of
# comments, and `s`, 1 in a string, carry over from one line to the next.
STRIP := awk '{ \
	out = ""; \
	for (i = 1; i <= length($$0); i++) { \
		c = substr($$0, i, 1); \
		if (c == "\"") { s = !s; continue } \
		if (s) continue; \
		if (substr($$0, i, 2) == "(*") { d++; i++; continue } \
		if (d && substr($$0, i, 2) == "*)") { d--; i++; continue } \
		if (!d) out = out c \
	} \
	print out }'

# The theorems that Assumptions.v prints and the constructors of `made` and
# `dmade` that quantify over an MPFR must each have an `Example` in
# theories/MpfrExamples.v, which applies it to the ideal MPFR. `Search` prints
# each name that it finds as `name:` at the start of a line, with the type
# after it or on indented lines. By default it hides the names whose qualified
# name contains `Private_`, `_subproof` or `_subterm`, and Assumptions.v has
# it show them. `Search` lists no theorem that another file declares `Local`,
# so the check misses one that Assumptions.v prints. `assumptions` removes
# Assumptions.glob, MpfrSearch.out and MpfrSearchValid.out before it compiles
# Assumptions.v, and fails on an error in Assumptions.v. If one of them is
# still missing or empty when `examples` runs, usually because `examples` ran
# without `assumptions` (`make -o assumptions`), or, for the last two, because
# a `Redirect` is gone or a `Search` found nothing, the check stops there.
# MpfrExamples.out lists the names in MpfrSearch.out that IN_GLOB keeps, and
# those in MpfrSearchValid.out, from Valid.v, other than the induction
# principles of `made` and `dmade`, whose names end in `_ind` or `_sind`.
# IN_GLOB takes the theorems that Assumptions.v prints from the R lines of
# Assumptions.glob that have a name. Rocq writes one for each
# `Print Assumptions`, whatever form it takes, such as a qualified name, a
# notation, an abbreviation, a name on the next line, or two on one line. A
# comment makes no R line, so a `Print Assumptions` in a comment does not
# count.
# For each theorem, `Search` prints the shortest name that refers to it in
# Assumptions.v, such as `MonoInc.mono_inc_correct` for one of a file that
# Assumptions.v does not import, and Rocq 9.1 has no option
# `Printing Fully Qualified` to have it print full names. So IN_GLOB matches
# the names by their last part. This keeps every theorem that Assumptions.v
# prints and `Search` lists, as each name that refers to a theorem ends in
# the last part of its full name. It can also ask for an `Example` more, of
# a name in MpfrSearch.out that refers to no theorem that Assumptions.v
# prints, in two ways: if its last part is that of another reference of
# Assumptions.v, such as the `Model.mpfr` of the `Search`es (no name in
# MpfrSearch.out has the last part `mpfr`), or that of a theorem of another
# module that Assumptions.v prints, such as one of the dyadic kernel, which
# it prints by qualified name. A name that contains a `.` cannot be that of
# an `Example`, so the check fails if IN_GLOB keeps one.
# The names in MpfrExamples.out must be those of the `Example`s, of which only
# the lines `Example <name>_ideal := ltac:(mpfr_example <name>).` are read.
# MpfrExamples.v is read without its comments and strings (STRIP), so an
# `Example` in a comment or a string does not count.
examples: assumptions
	for f in Assumptions.glob MpfrSearch.out MpfrSearchValid.out; do test -s $$f || { \
		echo "$$f" 'is missing or empty. Compiling Assumptions.v writes it, so the' \
			'usual causes are `examples` run without `assumptions`, which compiles' \
			'Assumptions.v, or, for MpfrSearch.out and MpfrSearchValid.out, which' \
			'a `Redirect` at the end of Assumptions.v writes, a removed `Redirect`' \
			'or a `Search` that finds nothing.' >&2; \
		exit 1; }; done
	{ sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearch.out | $(IN_GLOB); \
		sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearchValid.out | grep -v -e '_ind$$' -e '_sind$$'; } \
		| LC_ALL=C sort -u > MpfrExamples.out
	$(STRIP) theories/MpfrExamples.v \
		| sed -n 's/^Example \([A-Za-z0-9_]*\)_ideal := ltac:(mpfr_example \1)\.$$/\1/p' \
		| LC_ALL=C sort | diff -u MpfrExamples.out - || { \
		echo 'The names above differ between MpfrExamples.out (-), which must each' \
			'have an `Example`, and the `Example`s in theories/MpfrExamples.v (+).' \
			'Write each as `Example <name>_ideal := ltac:(mpfr_example <name>).` on' \
			'one line, and remove those of names that are not in MpfrExamples.out.' >&2; \
		exit 1; }

clean:
	if [ -f RocqMakefile ]; then $(MAKE) -f RocqMakefile cleanall; fi
	rm -f RocqMakefile RocqMakefile.conf .RocqMakefile.d
	rm -f Assumptions.vo Assumptions.vok Assumptions.vos Assumptions.glob
	rm -f .Assumptions.aux Assumptions.out
	rm -f MpfrSearch.out MpfrSearchValid.out MpfrExamples.out

.PHONY: all proofs assumptions examples clean
