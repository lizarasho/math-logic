.PHONY: all run clean pack

all: Lexer.hs Parser.hs
	ghc Main.hs -o solution

run: 
	./solution

Lexer.hs Parser.hs: Lexer.x Parser.y
	alex -g Lexer.x -o Lexer.hs
	happy -g -a -c Parser.y -o Parser.hs

clean:
	rm *.o *.hi

pack:
	zip A Makefile Lexer.x Parser.y
