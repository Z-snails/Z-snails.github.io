{ pkgs ? import <nixpkgs> {}}:

pkgs.mkShell { packages = [ pkgs.libffi pkgs.ruby ]; }
