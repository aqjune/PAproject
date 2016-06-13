.PHONY: all clean

all:
	ocamlbuild main.native -package ocamlgraph

clean:
	rm -rf _build main.native graph.dot graph.png
