//void *malloc(unsigned);

void __blast_assert()
{
 assert(0);
}

struct list_head {
};

struct list_head *elem = (struct list_head *)((void *)0);

void list_add(struct list_head *news, struct list_head *head) {
  if(news!=((void *)0)) {
   ((news!=elem) ? (0) : __blast_assert ());
   if(__VERIFIER_nondet_int())
         elem = news;
  }
}

struct drm_device {
 struct list_head vmalist;
};

struct drm_vma_entry {
 struct list_head head;
};

void drm_vm_open_locked(struct drm_device *dev)
{
 struct drm_vma_entry *vma_entry;
 vma_entry = (struct drm_vma_entry *)malloc(sizeof(*vma_entry));
 if (vma_entry) {
  list_add(&vma_entry->head, &dev->vmalist);
 }
}

int main(void) 
{
 struct drm_device dev;
 drm_vm_open_locked(&dev);
 drm_vm_open_locked(&dev);
}
