
all:
	lean --make > errors.txt

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `/usr/bin/find . -name "*.lean"`