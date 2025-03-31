AGDA2HS?=agda2hs-1.3
DIST?=dist/

all: compile

compile:
	$(AGDA2HS) -o $(DIST) index.agda

typecheck:
	$(AGDA2HS) -d index.agda

clean:
	rm -rf _build/ $(DIST)
