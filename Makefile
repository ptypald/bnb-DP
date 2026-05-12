CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra
LDLIBS ?= -lm

BUILD_DIR := build
DP_BIN := $(BUILD_DIR)/bnb_dp
DFS_BIN := $(BUILD_DIR)/bnb_dfs

.PHONY: all clean dp dfs

all: dp dfs

dp: $(DP_BIN)

dfs: $(DFS_BIN)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(DP_BIN): main-dp.c | $(BUILD_DIR)
	$(CC) $(CFLAGS) $< -o $@ $(LDLIBS)

$(DFS_BIN): main-bnb-dp.c | $(BUILD_DIR)
	$(CC) $(CFLAGS) $< -o $@ $(LDLIBS)

clean:
	rm -rf $(BUILD_DIR)
