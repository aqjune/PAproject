.PHONY: all clean

all:
	ocamlbuild main.native -package ocamlgraph -tag debug

clean:
	rm -rf _build main.native graph.dot graph.png
