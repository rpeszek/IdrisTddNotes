
DEFAULT: build

clean:
	idris --clean IdrisTddNotes.ipkg

all: install

install: build
	idris --install IdrisTddNotes.ipkg

build: 
	idris --build IdrisTddNotes.ipkg
