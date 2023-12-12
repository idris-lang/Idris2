all: libexternalc.so

externalc.o: externalc.c externalc.h
	cc -c -fPIC $< -o $@

libexternalc.so: externalc.o
	cc $< -shared -o $@

clean:
	rm -f externalc.o externalc.so