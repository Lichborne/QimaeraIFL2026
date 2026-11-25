.PHONY: main clean

main:
	idris2 -p contrib -p linear Main.idr -o main

clean:
	rm -rf build/
