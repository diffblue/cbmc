/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_IREP_PIPE_H
#define CPROVER_CEGIS_CEGIS_UTIL_IREP_PIPE_H

/**
 * @brief Helper for sending irep SDUs through pipes.
 *
 * @details Wraps the process of creating and closing pipes
 * as well as sending irep service data units through it.
 *
 * XXX: Windows implementation currently pending!
 */
class irep_pipet
{
  int fd[2u];
  bool read_closed;
  bool write_closed;
  bool close_on_destuction;
public:
  /**
   * @brief Creates an irep pipe.
   *
   * @details Creates an irep pipe which doesn't close
   * on destruction.
   */
  irep_pipet();

  /**
   * @brief Creates an irep pipe.
   *
   * @details Creates an irep pipe which optionally
   * closes on desctruction
   *
   * @param auto_close <code>true</code> if irep pipe
   * should close automaticall, <code>false</code>
   * otherwise.
   */
  explicit irep_pipet(bool auto_close);

  /**
   * @brief Optionally closing destructor.
   *
   * @details Closes <code>this</code> irep pipe if
   * configured accordingly.
   */
  ~irep_pipet();

  /**
   * @brief Closes the read end.
   *
   * @details Closes <code>this</code> irep pipe's
   * read end. Afterwards only writing is permitted.
   */
  void close_read();

  /**
   * @brief Provides read end status.
   *
   * @details Indicates whether read end is closed.
   *
   * @return <code>true</code> if read end is closed,
   * <code>false</code> otherwise.
   */
  bool is_read_closed() const;

  /**
   * @brief Closes the write end.
   *
   * @details Closes <code>this</code> irep pipe's
   * read end. Afterwards only reading is permitted.
   */
  void close_write();

  /**
   * @brief Provides read end status.
   *
   * @details Indicates whether read end is closed.
   *
   * @return <code>true</code> if read end is closed,
   * <code>false</code> otherwise.
   */
  bool is_write_closed() const;

  /**
   * @brief Closes the pipe entirely.
   *
   * @details Closes both the write and the read end
   * of <code>this</code> pipe.
   */
  void close();

  /**
   * @brief Transmits the given irep.
   *
   * @details Serialises the given irep SDU and transmits
   * it to the peer.
   *
   * @param sdu The irep SDU to transmit.
   */
  void send(const class irept &sdu) const;

  /**
   * @brief Receives an irep SDU.
   *
   * @details Deserialises an SDU transmitted through the pipe
   * into <code>sdu</code>.
   *
   * @param sdu The irep to which the deserialised SDU
   * should be written.
   */
  void receive(irept &sdu) const;

  /**
   * @brief Enable auto-closing mode.
   *
   * @details Indicates that <code>this</code> irep pipe should
   * be closed automatically.
   */
  void auto_close();
};

#endif // CPROVER_CEGIS_CEGIS_UTIL_IREP_PIPE_H
