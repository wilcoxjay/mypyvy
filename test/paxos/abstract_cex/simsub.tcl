#!/usr/bin/env tclsh

while {[gets stdin line] >= 0} {
    puts [string map $argv $line]
}

