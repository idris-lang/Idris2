all: libexternalc.so

externalc.o: externalc.c externalc.h
	$(CC) -c -fPIC $< -o $@

libexternalc.so: externalc.o
	$(CC) $< -shared -o $@

clean:
	rm -f externalc.o externalc.so