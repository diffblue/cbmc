#ifndef CPROVER_UTIL_BLOCKING_QUEUE
#define CPROVER_UTIL_BLOCKING_QUEUE

#include <mutex>
#include <condition_variable>
#include <queue>

template <typename T> class blocking_queue {
  std::condition_variable can_pop;
  std::mutex sync;
  std::queue<T> qu;
  bool shutdown = false;

public:
  void push(const T& item)
  {
    {
      std::unique_lock<std::mutex> lock(sync);
      qu.push(item);
    }
    can_pop.notify_one();
  }

  void request_shutdown()
  {
    {
      std::unique_lock<std::mutex> lock(sync);
      shutdown = true;
    }
    can_pop.notify_all();
  }

  bool pop(T &item)
  {
    std::unique_lock<std::mutex> lock(sync);
    for (;;)
    {
      if (qu.empty())
      {
        if (shutdown)
        {
          return false;
        }
      }
      else
      {
        break;
      }
      can_pop.wait(lock);
    }
    item = std::move(qu.front());
    qu.pop();
    return true;
  }
};

#endif // CPROVER_UTIL_BLOCKING_QUEUE
