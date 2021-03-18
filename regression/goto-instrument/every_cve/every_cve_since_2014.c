int SSLHASHSHA1_update();
int tls1_write_bytes();
int speculate();
const int TLS1_RT_HEARTBEAT;

#define EFAULT 1
#define EBUSY 3
#define ENOENT 4

int main()
{
  int err;
  const int payload_len = 16;
  const int msg_len;
  int payload[payload_len];
  int message[msg_len];
  int *tsk;
  int *mm;
  int *page_mask;
  unsigned long start;
  unsigned long nr_pages;
  unsigned int gup_flags;
  int *nonblocking;

  // 2014-0160
  int i = 0;
  for(; i < err; ++i)
    tls1_write_bytes(message[i], TLS1_RT_HEARTBEAT, payload[i]);

  // 2014-6271
  system("env x='() { :;}; echo shellshock'");

  // 2014-1266
  // not a great year for the industry
  if((err = SSLHashSHA1_update()) != 0)
    goto fail;
    goto fail;


  // 2017-5753
  if(payload_len < msg_len)
  {
    int val = message[payload_len];
    if(speculate(val))
      sleep(2);
  }

  // 2016-5195
  do {
    int *page;
    unsigned int foll_flags = gup_flags;
    int vma = find_extend_vma(mm, start);

retry:
    cond_resched();
    page = follow_page_mask(vma, start, foll_flags, &page_mask);
    if (!page) {
        int ret;
        ret = faultin_page(tsk, vma, start, &foll_flags,
                nonblocking);
        switch (ret) {
        case 0:
            goto retry;
        case -EFAULT:
            return i ? i : ret;
        case -EBUSY:
            return i;
        case -ENOENT:
            goto next_page;
        }
        BUG();
    }

next_page:
    nr_pages -= start;
  } while (nr_pages);

fail:
  return 1;

  return 0;
}
