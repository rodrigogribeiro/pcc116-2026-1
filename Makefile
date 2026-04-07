PANDOC = pandoc
PANDOC_FLAGS = -t revealjs -s --slide-level=1 --mathjax -V theme=white

SLIDES_DIR = slides
MD_FILES = $(shell find $(SLIDES_DIR) -name '*.md')
HTML_FILES = $(MD_FILES:.md=.html)

.PHONY: all clean

all: $(HTML_FILES)

%.html: %.md
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<

clean:
	rm -f $(HTML_FILES)
