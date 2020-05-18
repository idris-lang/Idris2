#include <assert.h>
#include <stdio.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "idris_net.h"

void test_sockaddr_port_returns_random_port_when_bind_port_is_0() {
  int sock = idrnet_socket(AF_INET, 1,  0);
  assert(sock > 0);

  int res = idrnet_bind(sock, AF_INET, 1, "127.0.0.1", 0);
  assert(res == 0);

  res = idrnet_sockaddr_port(sock);
  assert(res > 0);

  close(sock);
}

void test_sockaddr_port_returns_explicitly_assigned_port() {
  int sock = idrnet_socket(AF_INET, 1,  0);
  assert(sock > 0);

  int res = idrnet_bind(sock, AF_INET, 1, "127.0.0.1", 34567);
  assert(res == 0);

  res = idrnet_sockaddr_port(sock);
  assert(res == 34567);

  close(sock);
}

void test_peek_and_poke_buffer() {
  void *buf = idrnet_malloc(100);
  assert(buf > 0);

  for (int i = 0; i < 100; i++) {
    idrnet_poke(buf,i,7*i);
  }

  for(int i = 0; i < 100; i++) {
    assert (idrnet_peek(buf,i) == (0xff & 7*i));
  }
  idrnet_free(buf);
}


int main(void) {
  test_sockaddr_port_returns_explicitly_assigned_port();
  test_sockaddr_port_returns_random_port_when_bind_port_is_0();
  test_peek_and_poke_buffer();

  printf("network library tests SUCCESS\n");
  return 0;
}
