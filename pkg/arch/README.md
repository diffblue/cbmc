# Arch Linux Package

Update packages and install build dependencies

```bash
sudo pacman -Sy archlinux-keyring && sudo pacman -Syyu
sudo pacman -S gcc bison flex make patch perl-libwww fakeroot
```

Create folder for package and copy [PKGBUILD](PKGBUILD) file there.

Build package by running `makepkg` in that folder. That will compile *CBMC* and
run all tests. To install package run

```bash
sudo pacman -U cbmc-5.7-1-x86_64.pkg.tar.xz`
```
