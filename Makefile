
all:
	lean --make > errors.txt

clean:
	/usr/bin/find . -name "*.olean" -delete
