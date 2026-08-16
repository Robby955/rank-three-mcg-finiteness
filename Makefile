PYTHON ?= python3
TEX := manuscript/rank3_genus5_reader.tex
BUILD_DIR := build
SOURCE_DATE_EPOCH ?= 1786838400
GENUS4_TEX := manuscript/rank3_genus4_extension.tex
GENUS4_BUILD_DIR := build/genus4
GENUS4_SOURCE_DATE_EPOCH ?= 1786838400
SQUARE_TEX := manuscript/general_rank_square_endpoint.tex
SQUARE_BUILD_DIR := build/square-endpoint
SQUARE_SOURCE_DATE_EPOCH ?= 1786320000

.PHONY: build build-genus4 build-square-endpoint verify verify-math verify-release verify-genus4-candidate verify-square-endpoint clean clean-genus4 clean-square-endpoint

build:
	mkdir -p $(BUILD_DIR)
	SOURCE_DATE_EPOCH=$(SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(BUILD_DIR) $(TEX)

build-genus4:
	mkdir -p $(GENUS4_BUILD_DIR)
	SOURCE_DATE_EPOCH=$(GENUS4_SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(GENUS4_BUILD_DIR) $(GENUS4_TEX)

build-square-endpoint:
	mkdir -p $(SQUARE_BUILD_DIR)
	SOURCE_DATE_EPOCH=$(SQUARE_SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(SQUARE_BUILD_DIR) $(SQUARE_TEX)

verify:
	$(PYTHON) verification/verify_release.py

verify-math:
	$(PYTHON) verification/math/verify_hn_branches.py
	$(PYTHON) verification/math/verify_q10_jet.py
	$(PYTHON) verification/math/verify_q9.py

verify-release:
	$(MAKE) verify-math
	$(PYTHON) verification/verify_release.py --compile --pixels
	$(PYTHON) verification/verify_square_endpoint_packet.py --compile
	$(PYTHON) verification/verify_genus4_candidate.py --compile

verify-genus4-candidate:
	$(PYTHON) verification/verify_genus4_candidate.py --compile

verify-square-endpoint:
	$(PYTHON) verification/verify_square_endpoint_packet.py --compile

clean:
	latexmk -C -outdir=$(BUILD_DIR) $(TEX)

clean-genus4:
	latexmk -C -outdir=$(GENUS4_BUILD_DIR) $(GENUS4_TEX)

clean-square-endpoint:
	latexmk -C -outdir=$(SQUARE_BUILD_DIR) $(SQUARE_TEX)
