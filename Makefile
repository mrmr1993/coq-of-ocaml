OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild src/$(OUTPUT) -lflags -I,+compiler-libs,ocamlcommon.cmxa -use-ocamlfind -package smart_print,compiler-libs,yojson,str

clean:
	ocamlbuild -clean
	rm -f a.out tests/ex*.cmo tests/ex*.cmi tests/ex*.cmt tests/Nex* tests/ex*.glob tests/ex*.vo

test: tests/dependEx38.cmt tests/DependEx38.vo
	ruby test.rb

cmt: $(TESTS_INPUT:.ml=.cmt)
exp: $(TESTS_INPUT:.ml=.exp)
effects: $(TESTS_INPUT:.ml=.effects)
monadise: $(TESTS_INPUT:.ml=.monadise)
interface: $(TESTS_INPUT:.ml=.interface)
v: $(TESTS_INPUT:.ml=.v)
vo: $(TESTS_INPUT:.ml=.vo)

%.cmt: %.ml
	ocamlc -bin-annot $<

%.exp: %.cmt default
	./$(OUTPUT) -I tests Tests --mode exp $< >$@

%.effects: %.cmt default
	./$(OUTPUT) -I tests Tests --mode effects $< >$@

%.monadise: %.cmt default
	./$(OUTPUT) -I tests Tests --mode monadise $< >$@

%.interface: %.cmt default
	./$(OUTPUT) -I tests Tests --mode interface $< >$@

%.v: %.cmt default
	./$(OUTPUT) -I tests Tests --mode v $< >$@

%.vo: %.v
	coqc -R tests Tests -R OCaml OCaml $<
