struct gendisk {
  int major;
  char disk_name[32U];
} ;

void main() {
  struct gendisk a;
  struct gendisk *disk=&a;
  char (*__cil_tmp24)[32U];
  __cil_tmp24 = &(disk->disk_name);
  assert(__cil_tmp24!=0);
}

