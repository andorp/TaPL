idris2 = idris2
ipkg = tapl.ipkg

build: src $(ipkg) FORCE
	$(idris2) --build $(ipkg)

FORCE:

clean:
	$(idris2) --clean $(ipkg)
	rm -r .build

typecheck:
	$(idris2) --typecheck $(ipkg)
