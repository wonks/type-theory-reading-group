index.html: index.org main.css
	pandoc -t html5 \
	-s --toc --toc-depth=2 \
	-c main.css \
	index.org -o index.html

clean:
	rm -f index.html

.PHONY: clean
